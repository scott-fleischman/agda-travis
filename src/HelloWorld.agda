{-# OPTIONS --no-termination-check #-}

module HelloWorld where

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

postulate
  putStrLn : String → IO ⊤
  _⟫=_  : {A B : Set} → IO A → (A → IO B) → IO B

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStrLn = putStrLn #-}
{-# COMPILE GHC _⟫=_  = \_ _ _ _ -> (>>=) #-}

main : IO ⊤
main
  = putStrLn "Hello, world!"
  ⟫= λ _ → main
