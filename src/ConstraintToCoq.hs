{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module ConstraintToCoq (plugin) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Control.Exception
import Control.DeepSeq

import Data.Char
import Data.List
import Data.Maybe

import Data.Graph (stronglyConnComp, SCC, flattenSCC)

import Data.Map (Map)
import qualified Data.Map as M

import qualified Data.Set as S

import qualified Data.IntMap as IM

import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import Data.IORef

import Unsafe.Coerce

import System.IO
import System.Directory
import System.FilePath
import System.Process
import System.Exit

import GhcPlugins hiding ((<>))
import CoAxiom
import TcRnTypes
import GHC
import TcPluginM
import TyCoRep
import TcRnMonad (failWithTc, addWarnTc, liftIO, whenNoErrs)
import Unique
import UniqMap
import TcEvidence hiding ((<.>))
import Outputable (ppr, text)

import qualified HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Pretty
import HsToCoq.PrettyPrint hiding (text, hang, vcat,(<+>))
import HsToCoq.ConvertHaskell.Variables

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const (Just constraintPlugin) }

constraintPlugin :: TcPlugin
constraintPlugin =
  TcPlugin
    { tcPluginInit = pluginInit
    , tcPluginSolve = pluginSolver
    , tcPluginStop = pluginStop
    }

data ConstraintState
  = ConstraintState
  { triggerClass :: Class
  , eqClass :: Class
  , reqDeps :: UniqSet TyCon
  , satDeps :: UniqMap TyCon Coq.Sentence
  , curDep  :: Maybe TyCon
  , depGraph :: UniqMap TyCon (UniqSet TyCon)
  , assumptions :: Map String Coq.Assertion
  }

data ProverCt
  = ProverCt
  { proofName :: String
  , wantedCt  :: PredType
  , origCt :: Ct
  }

findClass :: Maybe FastString -> ModuleName -> OccName -> TcPluginM Class
findClass mpkg mn name = do
  Found _ mdl <- findImportedModule mn mpkg
  className <- lookupOrig mdl name
  tcLookupClass className

pluginInit :: TcPluginM (IORef ConstraintState)
pluginInit = do
  trigClass <- findClass (Just $ fsLit "constraint-to-coq")
                         (mkModuleName "ExternalProof")
                         (mkTcOcc "Proven")
  eqCls <- findClass (Just $ fsLit "base")
                     (mkModuleName "Data.Type.Equality")
                     (mkTcOcc "~")
  tcPluginIO $ newIORef $
    ConstraintState trigClass eqCls emptyUniqSet emptyUniqMap Nothing emptyUniqMap M.empty

pluginSolver :: IORef ConstraintState -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
pluginSolver is gs ws ds = do
  trigClass <- triggerClass <$> tcPluginIO (readIORef is)
  let interesting = mapMaybe (destructConstraint trigClass) $ ws++ds
  evs <- forM interesting $ \i -> do
    s <- tcPluginIO $ readIORef is
    when (M.notMember (proofName i) (assumptions s)) $
      case flip runStateT s $ (convCt gs i <* resolveDeps) of
        Right (assertion, s') -> tcPluginIO $
          writeIORef is (s'{ assumptions = M.insert (proofName i) assertion (assumptions s')})
        Left err -> unsafeTcPluginTcM $
          failWithTc $ hang (text "Constraint to Coq conversion failed with error") 4 err
    return $ mkEv (triggerClass s) (eqClass s) i
  return $ TcPluginOk (catMaybes evs) []

pluginStop :: IORef ConstraintState -> TcPluginM ()
pluginStop ics = do
  (top_env, _) <- getEnvs
  let file = unpackFS $ srcSpanFile $ tcg_top_loc top_env
      preamble_file = takeBaseName file <> "_preamble" <.> "v"
      theorem_file = takeBaseName file <> "_proofs" <.> "v"
  cs <- tcPluginIO $ readIORef ics
  tcPluginIO $ do
    withFile preamble_file WriteMode $ \h ->
      displayIO h $ renderPretty 1 100 $ vsep $ map renderGallina $ getPreamble cs
    tf_exists <- doesFileExist theorem_file
    if tf_exists
    then modifyTheoremFile theorem_file cs
    else do
      withFile theorem_file WriteMode $ \h -> do
        hPutStrLn h $ "Load " ++ takeBaseName preamble_file ++ "."
        displayIO h $ renderPretty 1 100 $ vsep $ map renderGallina $ getTheorems cs
  unsafeTcPluginTcM $
    whenNoErrs $
      checkFile cs theorem_file
  return ()

checkFile :: ConstraintState -> FilePath -> TcM ()
checkFile cs fp = do
  let allDefs = "(" ++ unwords (intersperse "," (M.keys $ assumptions cs)) ++ ")"
      checkCommand = "Definition all_ass := " ++ allDefs ++ ". Print Assumptions all_ass."
  (code,sout,serr) <- liftIO $
    readProcessWithExitCode "coqtop" ["-l",fp,"-quiet"] checkCommand
  case code of
    ExitFailure _ ->
      failWithTc $ makeFailErr fp serr
    ExitSuccess ->
      unless ("Closed under the global context" `isInfixOf` sout) $
        addWarnTc NoReason $ makeAssumptionWarning fp sout

makeFailErr :: FilePath -> String -> SDoc
makeFailErr fp err = 
  hang (text $ "coqtop failed while loading the file " ++ fp ++ " with the error:") 4
       (vcat $ map text $ lines err)

makeAssumptionWarning :: FilePath -> String -> SDoc
makeAssumptionWarning fp out =
  hang (text $ "The following theorems in " ++ fp ++ " are unproven:") 4
       (vcat $ map text $ drop 1 $ lines out)

modifyTheoremFile :: FilePath -> ConstraintState -> IO ()
modifyTheoremFile path cs = do
  oldContents <- readFile path
  void $ evaluate $ force oldContents
  writeFile path $ modifyContents cs oldContents

isCoqIdentChar :: Char -> Bool
isCoqIdentChar c = isAlphaNum c || c == '_' || c == '\''

modifyContents :: ConstraintState -> String -> String
modifyContents cs contents = unlines $ go S.empty (lines contents)
  where
    go seen [] = map renderCoq $ getTheorems (cs{assumptions = M.withoutKeys (assumptions cs) seen})
    go seen (x:xs) =
      case stripPrefix "Theorem " x of
        Nothing -> x : go seen xs
        Just remLines ->
          let theorem = takeWhile isCoqIdentChar $ dropWhile isSpace remLines
            in case M.lookup theorem (assumptions cs) of
                 Nothing -> x : go seen xs
                 Just assertion ->
                   renderCoq assertion : go (S.insert theorem seen) (dropWhile (not . isPrefixOf "Proof") xs)

renderCoq :: Gallina a => a -> String
renderCoq = TL.unpack . displayT . renderPretty 1 80 . renderGallina

importSentence :: Coq.Sentence
importSentence = Coq.ModuleSentence $ Coq.Require (Just "Coq") (Just Coq.Import) ("String" :| [])

hsType :: Coq.Sentence
hsType = Coq.InductiveSentence $ Coq.Inductive (hsTypeBody :| []) []
  where
    hsTypeId = (Coq.Bare "HsType")
    hsTypeBody = Coq.IndBody hsTypeId  [] (Coq.Qualid (Coq.Bare "Type")) hsTypeCons
    hsTypeCons =
      [(Coq.Bare "HsUnint",[],Just (Coq.Arrow (Coq.Qualid (Coq.Bare "string")) (Coq.Qualid hsTypeId)) )
      ,(Coq.Bare "HsApp",[],Just (foldr1 Coq.Arrow (replicate 3 $ Coq.Qualid hsTypeId)))
      ]

getPreamble :: ConstraintState -> [Coq.Sentence]
getPreamble cs = importSentence : hsType : (concatMap go $ topSortDeps $ depGraph cs)
  where go = combineSentences . mapMaybe (lookupUniqMap $ satDeps cs) . flattenSCC

getTheorems :: ConstraintState -> [Coq.Sentence]
getTheorems cs = map (`Coq.AssertionSentence` Coq.ProofAdmitted "") $ M.elems (assumptions cs)

combineSentences :: [Coq.Sentence] -> [Coq.Sentence]
combineSentences xs = catMaybes $ [Coq.InductiveSentence <$> inductives, Coq.FixpointSentence <$> fixpoints]
  where
    inductives = case getInductives xs of
      [] -> Nothing
      is -> Just $ foldr1
        (\(Coq.Inductive body notation) (Coq.Inductive body' notation') ->
          Coq.Inductive (body <> body') (notation <> notation'))
        is
    fixpoints = case getFixpoints xs of
      [] -> Nothing
      is -> Just $ foldr1
        (\(Coq.Fixpoint body notation) (Coq.Fixpoint body' notation') ->
          Coq.Fixpoint (body <> body') (notation <> notation'))
        is
    getInductives = mapMaybe getInductive
    getFixpoints = mapMaybe getFixpoint
    getInductive (Coq.InductiveSentence x) = Just x
    getInductive _ = Nothing
    getFixpoint (Coq.FixpointSentence x) = Just x
    getFixpoint _ = Nothing

mkEv :: Class -> Class -> ProverCt -> Maybe (EvTerm, Ct)
mkEv trigClass eqCls i = do
  (a,b) <- destructEq eqCls (wantedCt i)
  let eqCo = mkCoreConApps (classDataCon eqCls) [Type (GhcPlugins.typeKind a), Type a, Type b]
      dc = classDataCon trigClass
      prf = mkStrLitTy $ mkFastString $ proofName i
      ev = mkCoreConApps dc [Type prf, Type (wantedCt i), eqCo]
  return $ (EvExpr ev, origCt i)

type ConvFailure = Either SDoc
type ConvM a = StateT ConstraintState ConvFailure a

addDep :: TyCon -> ConstraintState -> ConstraintState
addDep t cs =
  cs { reqDeps = if t `elemUniqMap` (satDeps cs)
                 then reqDeps cs
                 else addOneToUniqSet (reqDeps cs) t
     , depGraph = case curDep cs of
         Nothing -> depGraph cs
         Just tc
           | t /= tc ->
             addToUniqMap_Acc (flip addOneToUniqSet) unitUniqSet (depGraph cs) tc t
           | otherwise -> addToUniqMap_C (<>) (depGraph cs) tc emptyUniqSet
     }

addDepM :: TyCon -> ConvM ()
addDepM = modify' . addDep

setCurrent :: Maybe TyCon -> ConvM ()
setCurrent tc = modify' (\s -> s { curDep = tc})

minViewUS :: UniqSet a -> Maybe a
minViewUS = fmap fst . IM.minView . ufmToIntMap . getUniqSet

conversionFailureContext :: String -> SDoc -> SDoc
conversionFailureContext s doc =
  hang (text $ "Failure while trying to tranlate theorem "++s++":") 4 doc

addContext :: (SDoc -> SDoc) -> ConvM a -> ConvM a
addContext f = mapStateT go
  where
    go (Left x) = Left (f x)
    go (Right x) = Right x

topSortDeps :: UniqMap TyCon (UniqSet TyCon) -> [SCC TyCon]
topSortDeps graph = stronglyConnComp gr
  where
    ufm :: UniqFM (TyCon, UniqSet TyCon)
    ufm = unsafeCoerce graph

    f (tc, es) = (tc, getKey (getUnique tc), map getKey (nonDetKeysUniqSet es))

    gr = map f $ nonDetEltsUFM ufm

resolveDeps :: ConvM ()
resolveDeps = do
  mdep <- gets (minViewUS . reqDeps)
  case mdep of
    Nothing -> return ()
    Just tcon -> do
      setCurrent (Just tcon)
      coqSent <- resolveTyCon tcon
      setCurrent Nothing
      modify' (\s -> s { reqDeps = delOneFromUniqSet (reqDeps s) tcon, satDeps = addToUniqMap (satDeps s) tcon coqSent})
      resolveDeps

resolveTyCon :: TyCon -> ConvM Coq.Sentence
resolveTyCon tc
  | isAlgTyCon tc = do
      let dcs = visibleDataCons $ algTyConRhs tc
          binders = tyConBinders tc
          name = coqName tc
          res = tyConResKind tc
      coqRes <- kindToCoq True res
      coqBinders <- traverse binderToTypedCoq' binders
      coqDcons <- traverse convertDataCon dcs
      let body = Coq.IndBody name coqBinders coqRes coqDcons
      pure $ Coq.InductiveSentence $ Coq.Inductive (body :| []) []
  | isTypeFamilyTyCon tc = do
      let binders = tyConBinders tc
          res = tyConResKind tc
          visBinders = filter (isVisibleArgFlag . tyConBinderArgFlag) binders
          matchItems = map (($ Nothing) . ($ Nothing) . Coq.MatchItem . Coq.Qualid . coqName . binderVar) visBinders
      let n = length $ takeWhile (not . isVisibleArgFlag . tyConBinderArgFlag) binders
      coqBinders <- traverse binderToTypedCoq $ binders
      resTy <- kindToCoq False res
      defn <- genFamDef n tc
      let matchDefn = Coq.Match (NE.fromList $ matchItems) (Just $ Coq.ReturnType resTy) defn
      let body = Coq.FixBody (coqName tc) (NE.fromList coqBinders) Nothing (Just resTy) matchDefn
      pure $ Coq.FixpointSentence $ Coq.Fixpoint (body :| []) []
  | otherwise =
      throwError (text "Got dependency on Tycon" <+> ppr tc <+> text "which is neither algebraic nor a type family")

convertDataCon :: DataCon -> ConvM (Coq.Qualid,[Coq.Binder],Maybe Coq.Term)
convertDataCon dc = do
  let tc = promoteDataCon dc
      binders = tyConBinders tc
      res = tyConResKind tc
  coqBinders <- traverse binderToTypedCoq $ filter (isVisibleArgFlag . tyConBinderArgFlag) binders
  coqRes <- kindToCoq True res
  pure (coqName dc, coqBinders, Just coqRes)

genFamDef :: Int -> TyCon -> ConvM [Coq.Equation]
genFamDef n tc
  | Just bs <- isClosedSynFamilyTyConWithAxiom_maybe tc = do
      stmts <- mapM (compileBranch n) (fromBranches $ co_ax_branches bs)
      pure stmts
  | otherwise = throwError (text "Got non-closed type family" <+> ppr tc)

compileBranch :: Int -> CoAxBranch -> ConvM Coq.Equation
compileBranch n br = do
  pats <- traverse compilePat $ drop n (coAxBranchLHS br)
  rhsType <- typeToCoq (coAxBranchRHS br)
  pure $ Coq.Equation (Coq.MultPattern (NE.fromList pats) :| []) rhsType

compilePat :: Type -> ConvM Coq.Pattern
compilePat (TyVarTy v) = do
  pure $ Coq.QualidPat (coqName v)
compilePat (LitTy tlit) = pure $ typeLitToCoqPat tlit
compilePat (AppTy a b) = do
  ca <- compilePat a
  cb <- compilePat b
  pure $ patApp ca cb
compilePat (CastTy t _) = compilePat t
compilePat ty = do
  case splitTyConApp_maybe ty of
    Nothing -> throwError (text "Can't convert into a Coq pattern: " <+> ppr ty)
    Just (tcon,tys) ->
      if isPromotedDataCon tcon
      then do
        cts <- sequence $ zipWith (\r t -> if r == Nominal then pure Coq.UnderscorePat else compilePat t)
                                  (tyConRoles tcon ++ repeat Representational) tys
        addDepM $ dataConTyCon $ fromJust $ isPromotedDataCon_maybe tcon
        pure $ Coq.ArgsPat (coqName tcon) cts
      else do
        -- Type constructors are represented as (HApp constructor ...)
        cts <- traverse patToWrappedPat tys
        let convTcon = Coq.ArgsPat (Coq.Bare "HsUnint") [Coq.StringPat (coqIdent tcon)]
        let converted = foldl patApp convTcon cts
        return converted

kindToCoq :: Bool -> Kind -> ConvM Coq.Term
kindToCoq _b (TyVarTy v) = pure $ Coq.Qualid (coqName v)
kindToCoq b k =
  case splitTyConApp_maybe k of
    Just (tcon,ks)
      | isAlgTyCon tcon -> do
          addDepM tcon
          cks <- traverse (kindToCoq b) ks
          pure $ Coq.ExplicitApp (coqName tcon) cks
      | isPromotedDataCon tcon -> typeToCoq k
    _ -> pure $ Coq.Qualid (Coq.Bare $ if b then "Type" else "HsType")

coqToHsTypeWrap :: Kind -> Coq.Term -> Coq.Term
coqToHsTypeWrap k t =
  case splitTyConApp_maybe k of
    Just (tcon,_)
      | isAlgTyCon tcon ->
          Coq.App (Coq.Qualid $ Coq.Bare $ "inj"<>(coqIdent tcon)) (Coq.PosArg t :| [])
    _ -> t

coqToHsTypeWrapPat :: Kind -> Coq.Pattern-> Coq.Pattern
coqToHsTypeWrapPat k t =
  case splitTyConApp_maybe k of
    Just (tcon,_)
      | isAlgTyCon tcon ->
          Coq.ArgsPat (Coq.Bare $ "inj"<>(coqIdent tcon)) [t]
    _ -> t

tyConKindVars :: TyCon -> TyVarSet
tyConKindVars = tyCoVarsOfTypes . map varType . binderVars . tyConBinders

typeToCoq :: Type -> ConvM Coq.Term
typeToCoq (TyVarTy v) = do
  pure $ Coq.Qualid (coqName v)
typeToCoq (ForAllTy b t) = do
  ct <- typeToCoq t
  return $ Coq.Forall (binderToCoq b :| []) ct
typeToCoq (LitTy tlit) = pure $ typeLitToCoq tlit
typeToCoq (AppTy a b) = do
  ca <- typeToCoq a
  cb <- typeToCoq b
  pure $ conApp ca cb
typeToCoq (CastTy t _) = typeToCoq t
typeToCoq ty = do
  cls <- gets eqClass
  case destructEq cls ty of
    Just (a,b) -> do
      ca <- typeToCoq a
      cb <- typeToCoq b
      return $ coqEq ca cb
    Nothing ->
      case splitTyConApp_maybe ty of
        Nothing -> throwError $ text "Can't convert into a Coq Term:" <+> ppr ty
        Just (tcon,tys)
          ->
          if isTypeFamilyTyCon tcon
          then do
            let binders = tyConBinders tcon
                kvs = tyConKindVars tcon
                kindVars = map (`elemVarSet` kvs) $ binderVars binders
            cts <- sequence $ zipWith (\kv t -> if kv then kindToCoq False t else typeToCoq t)
                                      (kindVars ++ repeat False) tys
            addDepM tcon
            pure $ Coq.ExplicitApp (coqName tcon) cts
          else if isPromotedDataCon tcon
          then do
            cts <- sequence $ zipWith (\r t -> if r == Nominal then kindToCoq False t else typeToCoq t)
                                      (tyConRoles tcon ++ repeat Representational) tys
            addDepM $ dataConTyCon $ fromJust $ isPromotedDataCon_maybe tcon
            pure $ Coq.ExplicitApp (coqName tcon) cts
          else do
            -- Type constructors are represented as (HApp constructor ...)
            cts <- traverse typeToWrappedCoq tys
            let convTcon = Coq.ExplicitApp (Coq.Bare "HsUnint") [Coq.String (coqIdent tcon)]
            let converted = foldl conApp convTcon cts
            return converted

patToWrappedPat :: Type -> ConvM Coq.Pattern
patToWrappedPat t = do
  ct <- compilePat t
  pure $ coqToHsTypeWrapPat (GhcPlugins.typeKind t) ct

typeToWrappedCoq :: Type -> ConvM Coq.Term
typeToWrappedCoq t = do
  ct <- typeToCoq t
  pure $ coqToHsTypeWrap (GhcPlugins.typeKind t) ct

patApp :: Coq.Pattern -> Coq.Pattern -> Coq.Pattern
patApp a b = Coq.ArgsPat (Coq.Bare "HsApp") [a,b]

conApp :: Coq.Term -> Coq.Term -> Coq.Term
conApp a b = Coq.ExplicitApp (Coq.Bare "HsApp") [a,b]

typeLitToCoq :: TyLit -> Coq.Term
typeLitToCoq (StrTyLit s) = Coq.String $ T.pack $ unpackFS s
typeLitToCoq (NumTyLit n) = Coq.Num $ fromInteger n

typeLitToCoqPat :: TyLit -> Coq.Pattern
typeLitToCoqPat (StrTyLit s) = Coq.StringPat $ T.pack $ unpackFS s
typeLitToCoqPat (NumTyLit n) = Coq.NumPat $ fromInteger n

coqName :: NamedThing a => a -> Coq.Qualid
coqName = Coq.Bare . coqIdent

coqIdent :: NamedThing a => a -> Coq.Ident
coqIdent x = (bareName $ getName x)

binderToTypedCoq :: TyConBinder -> ConvM Coq.Binder
binderToTypedCoq (TvBndr tv AnonTCB) = do
  typ <- kindToCoq False $ varType tv
  pure $ Coq.Typed Coq.Ungeneralizable Coq.Explicit (Coq.Ident (coqName tv) :| []) typ
binderToTypedCoq (TvBndr tv (NamedTCB Required)) = do
  typ <- kindToCoq True $ varType tv
  pure $ Coq.Typed Coq.Ungeneralizable Coq.Explicit (Coq.Ident (coqName tv) :| []) typ
binderToTypedCoq (TvBndr tv (NamedTCB _)) = do
  typ <- kindToCoq True $ varType tv
  pure $ Coq.Typed Coq.Ungeneralizable Coq.Implicit (Coq.Ident (coqName tv) :| []) typ

binderToTypedCoq' :: TyConBinder -> ConvM Coq.Binder
binderToTypedCoq' (TvBndr tv AnonTCB) = do
  typ <- kindToCoq True $ varType tv
  pure $ Coq.Typed Coq.Ungeneralizable Coq.Explicit (Coq.Ident (coqName tv) :| []) typ
binderToTypedCoq' (TvBndr tv (NamedTCB Required)) = do
  typ <- kindToCoq False $ varType tv
  pure $ Coq.Typed Coq.Ungeneralizable Coq.Explicit (Coq.Ident (coqName tv) :| []) typ
binderToTypedCoq' (TvBndr tv (NamedTCB _)) = do
  typ <- kindToCoq False $ varType tv
  pure $ Coq.Typed Coq.Ungeneralizable Coq.Implicit (Coq.Ident (coqName tv) :| []) typ

binderToCoq :: TyVarBinder -> Coq.Binder
binderToCoq (TvBndr tv Required) = Coq.Inferred Coq.Explicit (Coq.Ident $ coqName tv)
binderToCoq (TvBndr tv _       ) = Coq.Inferred Coq.Implicit (Coq.Ident $ coqName tv)

tyvarsToBinders :: Coq.Explicitness -> [TyVar] -> ConvM [Coq.Binder]
tyvarsToBinders e = pure . map (Coq.Inferred e . Coq.Ident . coqName)

collectSuccessful :: [ConvM a] -> ConvM [a]
collectSuccessful = fmap catMaybes . traverse (\act -> catchError (Just <$> act) (\_ -> pure Nothing))

collectTyVars :: [Type] -> [TyVar]
collectTyVars ts = filter (not . flip elemVarSet (coVarsOfTypes ts)) $ tyCoVarsOfTypesWellScoped ts

convCt :: [Ct] -> ProverCt -> ConvM Coq.Assertion
convCt gs (ProverCt name wanted' _) = addContext (conversionFailureContext name) $ do
  let wVars = tyCoVarsOfType wanted'
  let relevantGivens' = map ctPred $ collectRelevantGivens wVars gs
  let (_, wanted : relevantGivens) = tidyOpenTypes emptyTidyEnv (wanted' : relevantGivens')
  binders <- tyvarsToBinders Coq.Explicit $ (collectTyVars $ wanted : relevantGivens)
  let wrapBinders = case NE.nonEmpty binders of
        Nothing -> id
        Just bs -> Coq.Forall bs
  wTerm <- typeToCoq wanted
  gsTerms <- collectSuccessful $ map typeToCoq relevantGivens
  return $
    Coq.Assertion Coq.Theorem (Coq.Bare (T.pack name)) [] $
      wrapBinders $ foldr Coq.Arrow wTerm gsTerms

collectRelevantGivens :: TyVarSet -> [Ct] -> [Ct]
collectRelevantGivens initVars = fst . go [] initVars
  where
    go acc _  [] = (acc,[])
    go acc vs (ct:cts)
      | vs' `intersectsVarSet` vs = go (ct:acc) (vs `unionVarSet` vs') cts
      | otherwise = case go acc vs cts of
          (ins,outs)
            | vs' `intersectsVarSet` (tyCoVarsOfTypes $ map ctPred ins) -> go (ct:ins) vs' outs
            | otherwise -> (ins,ct:outs)
      where vs' = tyCoVarsOfType (ctPred ct)

coqEq :: Coq.Term -> Coq.Term -> Coq.Term
coqEq a b = (Coq.App (Coq.Qualid $ Coq.Bare "eq") (Coq.PosArg a :| [Coq.PosArg b]))

destructConstraint :: Class -> Ct -> Maybe ProverCt
destructConstraint cls ct =
  case classifyPredType $ ctPred ct of
    ClassPred gcls ((LitTy (StrTyLit prf)) : ctpred : _) -> do
      guard (cls == gcls)
      return $ ProverCt (unpackFS prf) ctpred ct
    _ -> Nothing

destructEq :: Class -> PredType -> Maybe (Type, Type)
destructEq cls ct =
  case classifyPredType ct of
    EqPred _ t1 t2 -> return (t1,t2)
    ClassPred gcls [_,t1,t2]| cls == gcls -> Just (t1,t2)
    _ -> Nothing
