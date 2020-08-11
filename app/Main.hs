{-# LANGUAGE OverloadedStrings #-}

module Main where

import Language.Omega

import Data.Text.Prettyprint.Doc

main :: IO ()
main = print $ map pretty $ runExhaustiveSearch (eval emptyEnv  exCounterfactualPaper) (BoundedInt 0 6)


----------------------------------------------------
--------------------- Examples ---------------------
----------------------------------------------------

ex1 :: ΩTerm
ex1 = lett "x" (.=) 1 inn
        (iff ("x" .== 1) thenn 2 elsee "x" + 3)


exCounterfactualPaper :: ΩTerm
exCounterfactualPaper = lett "c" (.=) 1 inn $
                          lett "x" (.=) (Ωλ "ω" Ω $
                                           iff ((("ω" - "c") * ("ω" - "c")) .<= 1)
                                             thenn 1
                                             elsee (-1)) inn $
                            rand(ΩCond (ΩDo "x" "c" 4) (Ωλ "ω" Ω $ ΩApp "x" "ω" .== (-1)))

