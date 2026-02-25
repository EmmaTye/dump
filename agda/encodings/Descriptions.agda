open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Primitive

open import Data.List

open import FinUniverse

{-
-- Description mechanism taken from
-- The Gentle Art of Levitation
-- by Chapman et. al.
-- 2010
-}

module Descriptions where

module FinDescriptions (FinUniverse : FinUniverse) where

  variable
    X Y : Set
    𝓁 : Level

  open FinUniverse.FinUniverse FinUniverse
  
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
  π nE P = ? -- TODO: ⊤, but we need to inject it into the correct universe level
  π (cE t E) P = 
    Σ (P 𝟎) (λ _ → π E (λ x → P (𝟏+ x)))

  data Description : Set₁ where
    ⊤' : Description
    Σ' : Σ Uꟳ (λ T → El T → Description) → Description
    ind× : Description → Description
  
  variable
    𝒟 : Description
    𝓓 : El _ → Description

  ⟦_⟧ : Description → Set → Set
  ⟦ ⊤' ⟧ X = ⊤
  ⟦ Σ' (T , 𝓓) ⟧ X = Σ (El T) (λ t → ⟦ 𝓓 t ⟧ X)
  ⟦ ind× 𝒟 ⟧ X = Σ X (λ _ → ⟦ 𝒟 ⟧ X)

  TaggedDescription : Set₁
  TaggedDescription = Σ En (λ E → π E (λ _ → Description))

