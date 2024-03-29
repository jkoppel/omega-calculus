{-# LANGUAGE OverloadedStrings #-}

module Main where

import Language.Omega

import Data.Text.Prettyprint.Doc

main :: IO ()
main = print $ map pretty $ runExhaustiveSearch (eval emptyEnv ex2) (BoundedInt 0 6)


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

exBindingLocal :: ΩTerm
exBindingLocal = rand $ Ωλ "ω" Ω $
                            lett "x" (.=) "ω" inn $
                              lett "y" (.=) ("x" + 1) inn $
                                ΩDo "y" "x" ("x" + 4)


exRebindOuter :: ΩTerm
exRebindOuter = lett "x" (.=) 1 inn $
                  lett "y" (.=) ("x" + 2) inn $
                    lett "f" (.=) (Ωλ "z" Ω $
                                      ΩDo "y" "x" "z")
                    inn $
                      (ΩApp "f" 3) + (ΩApp "f" 4)


exRebindRefOriginal :: ΩTerm
exRebindRefOriginal = lett "c" (.=) 2 inn $
                        lett "d" (.=) ("c" * 3) inn $
                          (ΩDo "d" "c" ("c" * 2))


ex2 :: ΩTerm
ex2 = lett "unif" (.=) (Ωλ "j" ΩTInt (Ωλ "w" (ΩTInt :->: ΩTReal) (ΩApp "w" "j"))) inn $
        lett "x" (.=) (Ωλ "ωq" (ΩTInt :->: ΩTReal) (ΩApp (ΩApp "unif" 1) "ωq")) inn $
        lett "ω" (.=) (Ωλ "i" ΩTInt $ iff ("i" .== 1) thenn 0.2 elsee 0.5) inn $
          (ΩApp "x" "ω")
