{-# OPTIONS_GHC -fwarn-deriving-typeable -Werror #-}
module T9687 where
import Data.Typeable

instance Typeable (a,b,c,d,e,f,g,h)
