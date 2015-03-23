{-# LANGUAGE AutoDeriveTypeable, PolyKinds, TypeFamilies, StandaloneDeriving #-}

module T9999 where

import Data.Typeable

data family F a
type family T a

class C a where
  data F1 a
  type T1 a

instance C Monad where
  data F1 Monad = MkF
  type T1 Monad = Int
--  type F2 a

-- foo = typeRep (Proxy :: Proxy F)

-- bar = typeRep (Proxy :: Proxy F1)

-- main = typeRep (Proxy :: Proxy F1)


