open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

module semiring where

  record Semiring (R : Set) : Set where
    infixl 19 _+_
    infixl 20 _*_
    field
      _+_ : R → R → R
      _*_ : R → R → R
      𝟘 : R
      𝟙 : R

      -- (R,+,𝟘) is a commutative monoid
      𝟘idl : ∀ {ρ : R} → 𝟘 + ρ ≡ ρ
      𝟘idr : ∀ {ρ : R} → ρ + 𝟘 ≡ ρ
      +ass : ∀ {ρ π ο : R} → (ρ + π) + ο ≡ ρ + (π + ο)
      +comm : ∀ {ρ π : R} → ρ + π ≡ π + ρ
  
      -- (R,∙,𝟙) is a monoid
      𝟙idl : ∀ {ρ : R} → 𝟙 * ρ ≡ ρ
      𝟙idr : ∀ {ρ : R} → ρ * 𝟙 ≡ ρ
      *ass : ∀ {ρ π ο : R} → (ρ * π) * ο ≡ ρ * (π * ο)
      
      -- ∙ distributes over +
      -- TODO: is ∙ a right or left action as a module over +?
      -- Assuming it's right...
      *dist : ∀ {ρ π ο : R} → ρ * (π + ο) ≡ (ρ * π) + (ρ * ο)

      -- 𝟘 absorbs under ∙
      𝟘*l : ∀ {ρ : R} → 𝟘 * ρ ≡ 𝟘
      𝟘*r : ∀ {ρ : R} → ρ * 𝟘 ≡ 𝟘

      -- 𝟘 positivity
      𝟘η+ : ∀ {ρ π : R} → ρ + π ≡ 𝟘 → (ρ ≡ 𝟘 × π ≡ 𝟘)
      𝟘η* : ∀ {ρ π : R} → ρ * π ≡ 𝟘 → (ρ ≡ 𝟘 ⊎ π ≡ 𝟘)

