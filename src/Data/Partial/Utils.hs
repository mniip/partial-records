{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-|
Module      : Data.Partial
Description : Utility functions used by generated Template Haskell code
Copyright   : (C) mniip 2019
License     : BSD3
Maintainer  : mniip@email.com
Stability   : experimental

Utility functions used by generated Template Haskell code.
-}
module Data.Partial.Utils where

import Data.Type.Bool
import Data.Tagged
import Data.Partial
import GHC.TypeLits

type Opt b x = Tagged b (Tagged x (If b x ()))

{-# INLINE fillOpt #-}
fillOpt :: x -> Opt 'True x
fillOpt x = Tagged (Tagged x)

{-# INLINE noOpt #-}
noOpt :: Opt 'False x
noOpt = Tagged (Tagged ())

{-# INLINE joinOpt #-}
joinOpt
  :: forall b1 b2 x. KnownBool b1 => Opt b1 x -> Opt b2 x -> Opt (b1 || b2) x
joinOpt (Tagged (Tagged x)) (Tagged (Tagged y)) =
  Tagged $ Tagged $ observeBool @b1 x y


{-# INLINE fromOpt #-}
fromOpt :: forall b x. KnownBool b => x -> Opt b x -> x
fromOpt x (Tagged (Tagged y)) = observeBool @b y x

class Require (dc :: Symbol) (fld :: Symbol) (b :: Bool) where
  unOpt :: p dc -> p fld -> Opt b x -> x

instance Require dc fld 'True where
  {-# INLINE unOpt #-}
  unOpt _ _ (Tagged (Tagged x)) = x

instance
  TypeError
    ('Text dc ':<>: 'Text " does not have a required field " ':<>: 'Text fld)
  => Require dc fld 'False where
  unOpt _ _ = error "unreachable"
