{-# Language TypeInType #-}
{-# Language RankNTypes, KindSignatures, PolyKinds #-}

import GHC.Types (TYPE)
import Data.Kind

data Lan (g::TYPE rep -> TYPE rep') (h::TYPE rep -> TYPE rep'') a where
  Lan :: forall xx (g::TYPE rep -> TYPE rep') (h::TYPE rep -> Type) a.
         (g xx -> a) -> h xx -> Lan g h a
