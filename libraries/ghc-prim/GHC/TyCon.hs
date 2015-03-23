module GHC.TyCon( TyCon(..) ) where

import GHC.Prim

#include "MachDeps.h"

data TyCon = TyCon
#if WORD_SIZE_IN_BITS < 64
                   Word64#  Word64#
#else
                   Word#    Word#
#endif
                   Addr#    -- Package name
                   Addr#   -- Module name
                   Addr#   -- Type constructor name
