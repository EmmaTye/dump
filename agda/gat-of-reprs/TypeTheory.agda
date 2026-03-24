open import Relation.Binary.PropositionalEquality
  using (_≡_)

-- TODO generate sum and prod functions up to 64, and generate relevant equalities (some sort of template code?)
-- TODO add model of theory, using agda types and isomorphism interpretation
-- TODO add weights to theory and add implementation of minimising function
--
module TypeTheory where

  record PartialIso (Ty : Set) : Set₁ where
    field
      _≅_ : Ty → Ty → Set
      _⊑_ : Ty → Ty → Set

      refl≅ : ∀ {A : Ty} → A ≅ A
      sym≅ : ∀ {A B : Ty} → A ≅ B → B ≅ A
      trans≅ : ∀ {A B C : Ty} →
               A ≅ B → B ≅ C → A ≅ C

      refl⊑ : ∀ {A : Ty} → A ⊑ A
      antiSym : ∀ {A B : Ty} → A ⊑ B → B ⊑ A → A ≡ B
      trans⊑ : ∀ {A B C : Ty} →
               A ⊑ B → B ⊑ C → A ⊑ C

  record Signature : Set₁ where
    field
      Ty : Set
      Tm : Ty → Set
      𝟘 : Ty
      𝟙 : Ty
      tt : Tm 𝟙
      _＋_ : Ty → Ty → Ty
      _⋆_ : Ty → Ty → Ty
      sum₃ : Ty → Ty → Ty → Ty
      sum₄ : Ty → Ty → Ty → Ty → Ty
      prod₃ : Ty → Ty → Ty → Ty
      prod₄ : Ty → Ty → Ty → Ty → Ty

  record Theory (Sig : Signature)
                (PI : PartialIso (Signature.Ty Sig))
                : Set₁ where
    open Signature Sig
    open PartialIso PI

    field
      -- Commutative semi-ring on (＋,𝟘,⋆,𝟙)
      ＋idl : ∀ {A : Ty} → (𝟘 ＋ A) ≅ A
      ＋idr : ∀ {A : Ty} → (A ＋ 𝟘) ≅ A
      ＋comm : ∀ {A B : Ty} → (A ＋ B) ≅ (B ＋ A)
      ⋆idl : ∀ {A : Ty} → (𝟙 ⋆ A) ≅ A
      ⋆idr : ∀ {A : Ty} → (A ⋆ 𝟙) ≅ A
      ⋆comm : ∀ {A B : Ty} → (A ⋆ B) ≅ (B ⋆ A)
      ⋆absorbl : ∀ {A : Ty} → (𝟘 ⋆ A) ≅ 𝟘
      ⋆absorbr : ∀ {A : Ty} → (A ⋆ 𝟘) ≅ 𝟘
      ⋆＋dist : ∀ {A B C : Ty} →
                (A ⋆ (B ＋ C)) ≅ ((A ⋆ B) ＋ (A ⋆ C))

      -- Padding
      -- Note: 𝟙 ＋ 𝟙 is a Bit
      padl : ∀ {A : Ty} → A ⊑ ((𝟙 ＋ 𝟙) ⋆ A)
      padr : ∀ {A : Ty} → A ⊑ (A ⋆ (𝟙 ＋ 𝟙))
      extend : ∀ {A : Ty} → 𝟙 ⊑ (𝟙 ＋ 𝟙)

