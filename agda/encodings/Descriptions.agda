open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Primitive

open import Level
open import Data.Empty
open import Data.Sum

{-
-- Description mechanism taken from
-- The Gentle Art of Levitation
-- by Chapman et. al.
-- 2010
-}

module Descriptions where

  variable
    𝓁 : Level

  module Environments where
    data Tag : Set where
      ′_ : String → Tag

    data En : Set where
      nE : En
      cE : (t : Tag) → (E : En) → En

    variable
      E F : En
      t s : Tag

    data # : En → Set where
      𝟎 : # (cE t E)
      𝟏+_ : # E → # (cE t E)

    -- Small product of environments
    π : ∀ {𝓁} (E : En) → (P : # E → Set 𝓁) → Set 𝓁
    π {𝓁 = 𝓁} nE P = Lift 𝓁 ⊤
    π (cE t E) P =
      Σ (P 𝟎) (λ _ → π E (λ x → P (𝟏+ x)))

    -- Eliminator of small products
    switch : ∀ {𝓁} (E : En) → (P : # E → Set 𝓁) →
             π E P → (s : # E) → P s
    switch E P (p0 , rest) 𝟎 = p0
    switch (cE t E) P (p0 , rest) (𝟏+ s) = switch E (λ x → P (𝟏+ x)) rest s

  open Environments

  data Description : Set₁ where
    ⊤' : Description
    Σ' : Σ Set (λ A → A → Description) → Description
    ind× : Description → Description

  ⟦_⟧ : ∀ {𝓁} → Description → Set 𝓁 → Set 𝓁
  ⟦_⟧ {𝓁 = 𝓁} ⊤' X = Lift 𝓁 ⊤
  ⟦ Σ' (A , 𝒟ₐ) ⟧ X = Σ A (λ a → ⟦ 𝒟ₐ a ⟧ X)
  ⟦ ind× 𝒟 ⟧ X = Σ X (λ _ → ⟦ 𝒟 ⟧ X)

  TaggedDescription : Set₁
  TaggedDescription = Σ En (λ E → π E (λ _ → Description))

  toDesc : TaggedDescription → Description
  toDesc (E , 𝒟s) = Σ' (# E , switch E (λ _ → Description) 𝒟s)

  data μ (𝒟 : Description) : Set where
    con : (d : ⟦ 𝒟 ⟧ (μ 𝒟)) → μ 𝒟

  μ⁺ : TaggedDescription → Set
  μ⁺ T = μ (toDesc T)

