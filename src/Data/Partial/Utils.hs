{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
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
import GHC.TypeLits

data Opt b x where
  Has :: x -> Opt 'True x
  Hasn't :: Opt 'False x

{-# INLINE joinOpt #-}
joinOpt :: Opt b1 x -> Opt b2 x -> Opt (b1 || b2) x
joinOpt (Has x) _ = Has x
joinOpt Hasn't y = y

{-# INLINE fromOpt #-}
fromOpt :: x -> Opt b x -> x
fromOpt _ (Has x) = x
fromOpt y Hasn't = y

class Require (dc :: Symbol) (fld :: Symbol) (b :: Bool) where
  unOpt :: p dc -> p fld -> Opt b x -> x

instance Require dc fld 'True where
  {-# INLINE unOpt #-}
  unOpt _ _ (Has x) = x

instance
  TypeError
    ('Text dc ':<>: 'Text " does not have a required field " ':<>: 'Text fld)
  => Require dc fld 'False where
  unOpt _ _ = error "unreachable"
