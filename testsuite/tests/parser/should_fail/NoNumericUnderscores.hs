{-# Language NoNumericUnderscores #-}

module NoNumericUnderscores where

f :: Int -> ()
f 1_000 = ()
f _   = ()

