{-# LANGUAGE NoNumericUnderscores #-}

-- Test for NumericUnderscores extension.
-- See Trac #14473
-- This is a testcase for NO NumericUnderscores extension.

module NoNumericUnderscores where

f :: Int -> ()
f 1_000 = ()
f _   = ()
