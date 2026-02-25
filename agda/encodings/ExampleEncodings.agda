open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Data.Vec

open import encodings

module ExampleEncodings where

data Uꟳ : Set where
  Bool' : Uꟳ
  ⊤' : Uꟳ

El : Uꟳ → Set
El Bool' = Bool
El ⊤' = ⊤

size : Uꟳ → Nat
size Bool' = 1
size ⊤' = 0

finEnc : (T : Uꟳ) → El T → 𝔹 (size T)
finEnc Bool' true = I ∷ []
finEnc Bool' false = O ∷ []
finEnc ⊤' tt = []

finDec : (T : Uꟳ) → 𝔹 (size T) → Maybe (El T)
finDec Bool' (I ∷ []) = just true
finDec Bool' (O ∷ []) = just false
finDec ⊤' [] = just tt

BasicSorts : FinSorts
BasicSorts = MkFinSorts Uꟳ El size finEnc finDec

