open Agda.Primitive

open import Data.Nat
open import Data.Vec

module BaseTT where

  private
    variable
      𝓁 : Level

  record BaseTypes {𝓁} : Set (lsuc (lsuc 𝓁)) where
    field
      Ty : Set (lsuc 𝓁)
      Tm : Ty → Set 𝓁
      𝟘 : Ty
      𝟙 : Ty
      _＋_ : Ty → Ty → Ty
      _⋆_ : Ty → Ty → Ty
      -- metatheoretical vector
      Sum : {n : ℕ} → Vec Ty n → Ty
      Prod : {n : ℕ} → Vec Ty n → Ty
  open BaseTypes ⦃ ... ⦄

  record PartialIso {𝓁} (Ty : Set (lsuc 𝓁))
                    : Set (lsuc 𝓁) where
    field
      _≅_ : Ty → Ty → Set 𝓁
      _⊑_ : Ty → Ty → Set 𝓁

      refl≅ : ∀ {A : Ty} → A ≅ A
      sym≅ : ∀ {A B : Ty} → A ≅ B → B ≅ A
      trans≅ : ∀ {A B C : Ty} →
               A ≅ B → B ≅ C → A ≅ C

      refl⊑ : ∀ {A : Ty} → A ⊑ A
      trans⊑ : ∀ {A B C : Ty} →
               A ⊑ B → B ⊑ C → A ⊑ C

    _⊒_ : Ty → Ty → Set 𝓁
    A ⊒ B = B ⊑ A

  open PartialIso ⦃ ... ⦄

  record BaseTT {𝓁} : Set (lsuc (lsuc 𝓁)) where

    field
      ⦃ BT ⦄ : BaseTypes {𝓁}
      ⦃ PI ⦄ : PartialIso Ty
      -- Commutative rig on (＋,𝟘,⋆,𝟙)
      ＋idl : ∀ {A : Ty} → (𝟘 ＋ A) ≅ A
      ＋comm : ∀ {A B : Ty} → (A ＋ B) ≅ (B ＋ A)
      ＋ass : ∀ {A B C : Ty} → ((A ＋ B) ＋ C) ≅ (A ＋ (B ＋ C))
      ⋆idl : ∀ {A : Ty} → (𝟙 ⋆ A) ≅ A
      ⋆comm : ∀ {A B : Ty} → (A ⋆ B) ≅ (B ⋆ A)
      ⋆ass : ∀ {A B C : Ty} → ((A ⋆ B) ⋆ C) ≅ (A ⋆ (B ⋆ C))
      ⋆absorbl : ∀ {A : Ty} → (𝟘 ⋆ A) ≅ 𝟘
      ⋆＋dist : ∀ {A B C : Ty} →
                (A ⋆ (B ＋ C)) ≅ ((A ⋆ B) ＋ (A ⋆ C))

      -- ＋ and Sumₙ laws
      ＋Sum : ∀ {n : ℕ} {As : Vec Ty n} → Sum As ≅ foldr′ _＋_ 𝟘 As
      -- ⋆ and Prodₙ laws
      ⋆Prod : ∀ {n : ℕ} {As : Vec Ty n} → Prod As ≅ foldr′ _⋆_ 𝟙 As

      -- ≅ laws
      ＋≅l : ∀ {A B C : Ty} → A ≅ B → (A ＋ C) ≅ (B ＋ C)
      ⋆≅l : ∀ {A B C : Ty} → A ≅ B → (A ⋆ C) ≅ (B ⋆ C)

      -- ⊑ laws
      transportl : ∀ {A B C : Ty} → A ≅ B → A ⊑ C → B ⊑ C
      transportr : ∀ {A B C : Ty} → A ≅ B → C ⊑ A → C ⊑ B
      ＋⊑l : ∀ {A B C : Ty} → A ⊑ B → (A ＋ C) ⊑ (B ＋ C)
      ⋆⊑l : ∀ {A B C : Ty} → A ⊑ B → (A ⋆ C) ⊑ (B ⋆ C)
      ＋extendl : ∀ {A B : Ty} → A ⊑ (A ＋ B)
      𝟘⊑𝟙 : 𝟘 ⊑ 𝟙

    ＋idr : ∀ {A : Ty} → (A ＋ 𝟘) ≅ A
    ＋idr = trans≅ ＋comm ＋idl
    ⋆idr : ∀ {A : Ty} → (A ⋆ 𝟙) ≅ A
    ⋆idr = trans≅ ⋆comm ⋆idl
    ⋆absorbr : ∀ {A : Ty} → (A ⋆ 𝟘) ≅ 𝟘
    ⋆absorbr = trans≅ ⋆comm ⋆absorbl
    ＋≅r : ∀ {A B C : Ty} → B ≅ C → (A ＋ B) ≅ (A ＋ C)
    ＋≅r b≅c = trans≅ ＋comm (trans≅ (＋≅l b≅c) ＋comm)
    ⋆≅r : ∀ {A B C : Ty} → B ≅ C → (A ⋆ B) ≅ (A ⋆ C)
    ⋆≅r b≅c = trans≅ ⋆comm (trans≅ (⋆≅l b≅c) ⋆comm)
    ＋⊑r : ∀ {A B C : Ty} → A ⊑ B → (C ＋ A) ⊑ (C ＋ B)
    ＋⊑r a⊑b = transportr ＋comm (transportl ＋comm (＋⊑l a⊑b))
    ⋆⊑r : ∀ {A B C : Ty} → A ⊑ B → (C ⋆ A) ⊑ (C ⋆ B)
    ⋆⊑r a⊑b = transportr ⋆comm (transportl ⋆comm (⋆⊑l a⊑b))
    ＋extendr : ∀ {A B : Ty} → B ⊑ (A ＋ B)
    ＋extendr = transportr ＋comm ＋extendl
    -- Note: 𝟙 ＋ 𝟙 is a Bit
    -- TODO: can we add a syntax to agda inside a record
    -- for 𝟙 ＋ 𝟙 = 𝔹?
    padl : ∀ {A : Ty} → A ⊑ ((𝟙 ＋ 𝟙) ⋆ A)
    padl = transportl ⋆idl (⋆⊑l ＋extendl)
    padr : ∀ {A : Ty} → A ⊑ (A ⋆ (𝟙 ＋ 𝟙))
    padr = transportl ⋆idr (⋆⊑r ＋extendl)

