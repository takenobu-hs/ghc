{-# Language NumericUnderscores #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NegativeLiterals #-}

import GHC.Types
--import GHC.Int

main :: IO ()
main = do
    -- decimal
    print [ (I# 1_000_000#) == 1000000,
            (I# 299_792_458#) == 299792458
          ]

    -- hexadecimal
    print [ (I# 0x1_000_000#) == 0x1000000,
            (I# 0X3fff_ffff#) == 0x3fffffff
          ]

    -- octal
    print [ (I# 0o1_000_000#) == 0o1000000,
            (I# 0O1__0#) == 0O10
          ]

    -- binary
    print [ (I# 0b01_0000_0000#) == 0b0100000000,
            (I# 0b1_11_01_0000_0_111#) == 0b1110100000111
          ]

    -- float
    print [ (F# 3.141_592_653_589_793#) == 3.141592653589793,
            (F# 96_485.332_89#) == 96485.33289,
            (F# 6.022_140_857e+23#) == 6.022140857e+23
          ]

    -- word
    print [ (W# 1_000_000##) == 1000000,
            (W# 299_792_458##) == 299792458
          ]

