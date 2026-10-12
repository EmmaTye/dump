open Agda.Primitive
open import Agda.Builtin.Sigma
  renaming (Σ to _×ᴰ_; _,_ to _,ᴰ_)

open import Data.Fin
  renaming (_+_ to _+F_)
open import Data.Fin.Patterns
open import Data.Nat
open import Data.Product
  using (_×_; _,_)

module multi-sorted-algebra where

  -- Set of finite lists of A
  _* : {𝓁 : Level} → Set 𝓁 → Set 𝓁
  A * = {n : ℕ} → Fin n → A

  private
    variable
      𝓁 : Level
      𝕊 : Set 𝓁
      Σ : 𝕊 * × 𝕊 → Set

  Alg : (Σ : 𝕊 * × 𝕊 → Set) → (A : Set) → Set
  Alg Σ A = ?

