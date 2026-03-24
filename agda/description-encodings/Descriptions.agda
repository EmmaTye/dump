open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Primitive

open import Level
open import Data.Empty
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product
open import Data.Sum
open import Data.Vec
open import Function.Base
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Relation.Nullary

{-
-- Description mechanism taken from
-- The Gentle Art of Levitation
-- by Chapman et. al.
-- 2010
-}

module Descriptions where
  
  private
    variable
      𝓁 : Level
      n : Nat

  module Environments where
    data Tag : Set where
      _′ : String → Tag

    variable
      t s : Tag
      ts ss : Vec Tag _

    data # : Vec Tag n → Set where
      𝟎 : # (t ∷ ts)
      𝟏+_ : {t : Tag} → (rest : # ts) → # (t ∷ ts)

    toFin : {ts : Vec Tag n} → # ts → Fin n
    toFin 𝟎 = fzero
    toFin (𝟏+ rest) = fsuc (toFin rest)

  open Environments

  data Description {𝓁} : Set (lsuc 𝓁) where
    ⊤' : Description
    Σ' : Σ (Set 𝓁) (λ A → A → Description {𝓁}) → Description
    ind× : Description {𝓁} → Description

  Description₀ = Description {lzero}
  Description₁ = Description {lsuc lzero}

  ⟦_⟧ : ∀ {𝓁} → Description {𝓁} → Set 𝓁 → Set 𝓁
  ⟦_⟧ {𝓁 = 𝓁} ⊤' X = Lift 𝓁 ⊤
  ⟦ Σ' (A , 𝒟ₐ) ⟧ X = Σ A (λ a → ⟦ 𝒟ₐ a ⟧ X)
  ⟦ ind× 𝒟 ⟧ X = Σ X (λ _ → ⟦ 𝒟 ⟧ X)

--  TaggedDescription : Set₁
--  TaggedDescription = Σ En (λ E → π E (λ _ → Description₀))
--
--  toDesc : TaggedDescription → Description
--  toDesc (E , 𝒟s) = Σ' (# E , switch E (λ _ → Description) 𝒟s)
--
--  data μ (𝒟 : Description) : Set where
--    con : (d : ⟦ 𝒟 ⟧ (μ 𝒟)) → μ 𝒟
--
--  μ⁺ : TaggedDescription → Set
--  μ⁺ T = μ (toDesc T)

