{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE HexFloatLiterals #-}
{-# LANGUAGE NegativeLiterals #-}

-- Test for NumericUnderscores extension.
-- See Trac #14473
-- This is a testcase for boxed literals.

main :: IO ()
main = do
    -- decimal
    print [ 1_000_000 == 1000000,
            1__0 == 10,
            -1_0 == -10,
            299_792_458 == 299792458,
            8_04_1 == 8041,
            2017_12_31 == 20171231
          ]

    -- hexadecimal
    print [ 0x1_000_000 == 0x1000000,
            0x1__0 == 0x10,
            0xff_00_00 == 0xff0000,
            0X3fff_ffff == 0x3fffffff
          ]

    -- octal
    print [ 0o1_000_000 == 0o1000000,
            0O1__0 == 0O10
          ]

    -- binary
    print [ 0b01_0000_0000 == 0b0100000000,
            0b1_11_01_0000_0_111 == 0b1110100000111,
            0b1100_1011__1110_1111__0101_0011 ==
            0b110010111110111101010011
          ]

    -- float
    print [ 3.141_592_653_589_793 == 3.141592653589793,
            96_485.332_89 == 96485.33289,
            6.022_140_857e+23 == 6.022140857e+23
          ]

    -- hexadecimal float
    print [ 0xF_F.1 == 0xFF.1,
            0xF_01p-8 == 0xF01p-8,
            0x0.F_1p4 == 0x0.F1p4
          ]

    -- validity
    print [ 0.000_1 == 0.0001,
            1_0.000_1 == 10.0001,
            1e+23 == 1e+23,
            1_e+23 == 1e+23,
            1__e+23 == 1e+23,
            1.0_e+23 == 1.0e+23,
            1.0_e+2_3 == 1.0e+23,
            1_e23 == 1e23,
            1_e-23 == 1e-23,
            1_0_e23 == 10_e23,
            1_0_e-23 == 10_e-23,
            0b_01 == 0b01,
            0b__11 == 0b11,
            0x_ff == 0xff,
            0x__ff == 0xff
          ]
