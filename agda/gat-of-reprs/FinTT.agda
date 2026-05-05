open import Data.Fin
open import Data.Nat
open import Relation.Binary.PropositionalEquality

module FinTT where

  -- A finite type is isomorphic to some Fin size
  record FinTy (Ty : Set) : Set where
    field
      size : ℕ
      toTy : Fin size → Ty
      toFin : Ty → Fin size
      fin→ty : ∀ (i : Fin size) → toFin (toTy i) ≡ i
      ty→fin : ∀ (t : Ty) → toTy (toFin t) ≡ t

