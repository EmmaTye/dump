open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Data.Vec

open import FinUniverse

module Encodings where

data Bit : Set where
  O : Bit
  I : Bit

𝔹_ : Nat → Set
𝔹 n = Vec Bit n

variable
  n m : Nat
  𝕓 𝕓' 𝕓₁ 𝕓₂ : 𝔹 _

record FinEncodings (FinUniverse : FinUniverse) : Set₁ where
  open FinUniverse.FinUniverse FinUniverse
  field
    size : Uꟳ → Nat
    finEnc : (T : Uꟳ) → El T → 𝔹 (size T)
    finDec : (T : Uꟳ) → 𝔹 (size T) → Maybe (El T)

