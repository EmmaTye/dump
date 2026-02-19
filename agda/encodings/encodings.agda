
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Data.Vec

module encodings where

𝔹_ : Nat → Set
𝔹 n = Vec Bool n

variable
  n m : Nat
  𝕓 𝕓' 𝕓₁ 𝕓₂ : 𝔹 _

record FinSorts : Set₂ where
  field
    Uꟳ : Set₁
    El : Uꟳ → Set
    size : Uꟳ → Nat
    finEnc : (T : Uꟳ) → El T → 𝔹 (size T)
    finDec : (T : Uꟳ) → 𝔹 (size T) → Maybe (El T)

