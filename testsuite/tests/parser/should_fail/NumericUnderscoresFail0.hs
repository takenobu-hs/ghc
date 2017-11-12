{-# LANGUAGE NumericUnderscores #-}

main :: IO ()
main = do
    -- invalid case for NumericUnderscores extension
    print [
            -- integer
            1000000_,
            _1000000,

            -- float
            0_.0001,
            _0.0001,
            0.0001_,
            0._0001,

            -- float with exponent
            1e_+23,
            1e+23_,
            1e+_23
          ]
