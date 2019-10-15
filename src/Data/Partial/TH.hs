{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

{-|
Module      : Data.Partial.TH
Description : Template Haskell utilities for constructing records with default
  values
Copyright   : (C) mniip 2019
License     : BSD3
Maintainer  : mniip@email.com
Stability   : experimental

Template Haskell utilities for constructing records with default values.
-}
module Data.Partial.TH
  ( mkToPartial
  , mkFromPartial
  , mkToPartialWith
  ) where

import Data.List
import Data.Partial
import Data.Partial.Utils
import Data.Proxy
import Control.Monad
import Control.Monad.Trans.Writer
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

getRecord :: Name -> Q ([TyVarBndr], Type, Name, [(Name, Type)])
getRecord name =
  reify name >>= \case
    TyConI dec -> case dec of
      DataD _ tc tvb _ cs _ -> expectOne cs $ \c -> expectRec c $ \dc ts ->
        pure (tvb, foldl appTVB (ConT tc) tvb, dc, fromVBT <$> ts)
      NewtypeD _ tc tvb _ c _ -> expectRec c $ \dc ts ->
        pure (tvb, foldl appTVB (ConT tc) tvb, dc, fromVBT <$> ts)
      _ -> fail "expected a data or newtype declaration"
    _ -> fail "expected a tycon name"
  where
    appTVB :: Type -> TyVarBndr -> Type
    appTVB t (PlainTV v) = AppT t (VarT v)
    appTVB t (KindedTV v k) = AppT t (SigT (VarT v) k)

    fromVBT :: VarBangType -> (Name, Type)
    fromVBT (var, _, ty) = (var, ty)

    expectOne :: [a] -> (a -> Q b) -> Q b
    expectOne [x] k = k x
    expectOne _ _ = fail "expected 1 constructor"

    expectRec :: Con -> (Name -> [VarBangType] -> Q a) -> Q a
    expectRec (RecC dc ts) k = k dc ts
    expectRec _ _ = fail "expected a record constructor"

mangleDC :: Name -> Name
mangleDC nm = mkName $ "Partial_" ++ nameBase nm

mangleFld :: (String -> String) -> Name -> Name
mangleFld mangler nm = mkName $ mangler $ nameBase nm

boolTV :: Name -> TyVarBndr
boolTV btv = kindedTV btv (ConT ''Bool)

toTList :: [Q Type] -> Q Type
toTList = foldr (appT . appT promotedConsT) promotedNilT

mkDataInst :: [TyVarBndr] -> Type -> Name -> [Type] -> Q Dec
mkDataInst tvb ty dc flds = do
  (unzip -> (btvs, tys)) <- forM flds $ \fldty -> do
    btv <- newName "b"
    (btv,) <$> bangType (bang noSourceUnpackedness noSourceStrictness)
      (conT ''Opt `appT` varT btv `appT` pure fldty)
  let
    con = forallC (tvb ++ map boolTV btvs) (pure [])
      $ gadtC [dc] (pure <$> tys) 
      $ conT ''Partial `appT` pure ty `appT` toTList (varT <$> btvs)
  dataInstD (pure []) ''Partial [pure ty, varT =<< newName "bs"]
    Nothing [con] []

mkFlds :: (String -> String) -> Type -> Name -> [(Name, Type)] -> Q [Dec]
mkFlds mangler ty dc flds = concat <$> forM (zip [0..] flds)
  (\(i, (fld, fldty)) -> sequence
    [ pragInlD (mangleFld mangler fld) Inline FunLike AllPhases
    , sigD (mangleFld mangler fld) $ arrowT `appT` pure fldty `appT`
      (conT ''Partial `appT` pure ty `appT`
        toTList (fill i (promotedT 'True) (promotedT 'False)))
    , funD (mangleFld mangler fld) [do
      var <- newName "x"
      clause [varP var] (normalB $ foldl appE (conE dc) $ fill i
          (varE 'fillOpt `appE` varE var) (varE 'noOpt)) []
      ]
    ])
  where
    fill :: Int -> a -> a -> [a]
    fill i x y = [if i == j then x else y | j <- take (length flds) [0..]]

mkInst :: Type -> Name -> [(Name, Type)] -> Q Dec
mkInst ty dc flds = instanceD (pure []) (conT ''Graded `appT` pure ty)
  [ pragInlD '(?) Inline FunLike AllPhases
  , funD '(?) [do
    xs <- replicateM (length flds) $ newName "x"
    ys <- replicateM (length flds) $ newName "y"
    clause
      [conP dc (varP <$> xs), conP dc (varP <$> ys)]
      (normalB $ foldl appE (conE dc)
        $ zipWith (appE . appE (varE 'joinOpt)) (varE <$> xs) (varE <$> ys))
      []
  ]]

mkCon :: String -> [Maybe Exp] -> [TyVarBndr] -> Type -> Name -> [(Name, Type)] -> Q [Dec]
mkCon nm defs tvb ty dc flds = sequence
  [ pragInlD (mkName nm) Inline FunLike AllPhases
  ,
    do
      btvs <- forM flds $ \_ -> newName "b"
      let
        bts = varT <$> btvs
        ctxs = zipWith3 mkCtx defs btvs flds
        mkCtx (Just _) tv _ = conT ''KnownBool `appT` varT tv
        mkCtx Nothing tv (fld, _) = conT ''Require
          `appT` mkLit dc `appT` mkLit fld `appT` varT tv
      sigD (mkName nm)
        $ forallT (tvb ++ map boolTV btvs)
          (sequence ctxs) $ arrowT
            `appT` (conT ''Partial `appT` pure ty `appT` toTList bts)
            `appT` pure ty
  , funD (mkName nm) [do
      xs <- forM flds $ \_ -> newName "x"
      clause
        [conP (mangleDC dc) (varP <$> xs)]
        (normalB $ foldl appE (conE dc) $ zipWith3 mkDef defs xs flds)
        []
    ]
  ]
  where
    mkLit = litT . strTyLit . nameBase
    mkDef Nothing x (fld, _) = varE 'unOpt
      `appE` (conE 'Proxy `sigE` (conT ''Proxy `appT` mkLit dc))
      `appE` (conE 'Proxy `sigE` (conT ''Proxy `appT` mkLit fld))
      `appE` varE x
    mkDef (Just def) x _ = varE 'fromOpt `appE` pure def `appE` varE x

parseDefs :: Name -> [Name] -> Exp -> Q [Maybe Exp]
parseDefs dc flds (RecConE dc' eqs)
  | dc /= dc' = fail $ "Expected record construction of " ++ show dc
  | Just fld <- find (`notElem` flds) (fst <$> eqs)
    = fail $ "Not a field of " ++ show dc ++ ": " ++ show fld
  | otherwise = pure $ map (`lookup` eqs) flds
parseDefs _ _ _ = fail "Expected record construction"

-- | Generate an instance of the 'Partial' family and the 'Graded' class. Takes
-- a data constructor name. For example:
--
-- @
-- data Foo a = Foo a { fld1 :: Int, fld2 :: a }
-- mkToPartial ''Foo
-- @
--
-- expands to:
--
-- @
-- data instance 'Partial' (Foo a) bs where
--   Partial_Foo :: forall a b1 b2.
--     'Opt' b1 Int -> 'Opt' b2 a -> Partial (Foo a) '[b1, b2]
-- {-\# INLINE mkfld1 #-}
-- mkfld1 :: Int -> 'Partial' (Foo a) '[ 'True, 'False]
-- mkfld1 x = Partial_Foo ('fillOpt' x) 'noOpt'
-- {-\# INLINE mkfld2 #-}
-- mkfld2 :: a -> 'Partial' (Foo a) '[ 'False, 'True]
-- mkfld2 x = Partial_Foo 'noOpt' ('fillOpt' x)
-- instance 'Graded' (Foo a) where
--   {-\# INLINE ('?') #-}
--   Partial_Foo x1 x2 '?' Partial_Foo y1 y1
--     = Partial_Foo ('joinOpt' x1 y1) ('joinOpt' x2 y2)
-- @
mkToPartial :: Name -> Q [Dec]
mkToPartial = mkToPartialWith ("mk" ++)

-- | Generate a function that turns a 'Partial' into a value of the actual
-- datatype. Takes a name for the function to be defined, as well as the type
-- the result should have (can include type variables but all of them must be
-- quantified), as well as the "default values": a record construction
-- specifying just those fields that you want, with their default values.
-- For example:
--
-- @
-- data Foo a = Foo a { fld1 :: Int, fld2 :: a }
-- mkFromPartial "mkFoo" [t|forall a. Foo (Maybe a)|] [|Foo { fld2 = Nothing }|]
-- @
--
-- expands to:
--
-- @
-- {-\# INLINE mkFoo #-}
-- mkFoo :: forall a b1 b2.
--   ( 'Require' \"Foo\" \"fld1\" b1
--   -- ^ Assert that b1 ~ 'True but generate a nice error message if not
--   , 'KnownBool' b2 )
--   => 'Partial' (Foo (Maybe a)) '[b1, b2] -> Foo (Maybe a)
-- mkFoo (Partial_Foo x1 x2) = Foo ('unOpt' x1) ('fromOpt' Nothing x2)
-- @
mkFromPartial :: String -> Q Type -> Q Exp -> Q [Dec]
mkFromPartial nm qty def = do
  ty <- qty
  (tau, tvb) <- runWriterT $ splitTauType ty
  tc <- splitTyCon tau
  (_, _, dc, flds) <- getRecord tc
  defs <- parseDefs dc (fst <$> flds) =<< def
  mkCon nm defs tvb tau dc flds
  where
    splitTauType :: Type -> WriterT [TyVarBndr] Q Type
    splitTauType (ForallT tvb _ t) = tell tvb >> splitTauType t
    splitTauType (ParensT t) = splitTauType t
    splitTauType t = pure t
    
    splitTyCon (AppT f _) = splitTyCon f
    splitTyCon (SigT t _) = splitTyCon t
    splitTyCon (ConT tc) = pure tc
    splitTyCon (InfixT _ tc _) = pure tc
    splitTyCon (ParensT t) = splitTyCon t
    splitTyCon _ = fail "expected a tycon application"

-- | The default procedure for generating field constructors from field names is
-- prepending @"mk"@. You can override this behavior by passing a custom field
-- name generating function to this function.
mkToPartialWith :: (String -> String) -> Name -> Q [Dec]
mkToPartialWith mangler tc = do
  (tvb, ty, dc, flds) <- getRecord tc
  concat <$> sequence
    [ pure <$> mkDataInst tvb ty (mangleDC dc) (snd <$> flds)
    , mkFlds mangler ty (mangleDC dc) flds
    , pure <$> mkInst ty (mangleDC dc) flds
    ]