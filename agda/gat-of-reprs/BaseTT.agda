open Agda.Primitive

-- TODO generate sum and prod functions up to 64, and generate relevant equalities (some sort of template code?)

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
      Sum₃ : Ty → Ty → Ty → Ty
      Sum₄ : Ty → Ty → Ty → Ty → Ty
      Prod₃ : Ty → Ty → Ty → Ty
      Prod₄ : Ty → Ty → Ty → Ty → Ty

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

  record BaseTT {𝓁} (BT : BaseTypes {𝓁})
                    (PI : PartialIso (BaseTypes.Ty BT))
                : Set (lsuc 𝓁) where
    open BaseTypes BT
    open PartialIso PI

    field
      -- Commutative semi-ring on (＋,𝟘,⋆,𝟙)
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
      ＋Sum₃ : ∀ {A B C : Ty} → ((A ＋ B) ＋ C) ≅ Sum₃ A B C
      ＋Sum₄ : ∀ {A B C D : Ty} → (((A ＋ B) ＋ C) ＋ D) ≅ Sum₄ A B C D
      -- ⋆ and Prodₙ laws
      ⋆Prod₃ : ∀ {A B C : Ty} → ((A ⋆ B) ⋆ C) ≅ Prod₃ A B C
      ⋆Prod₄ : ∀ {A B C D : Ty} → (((A ⋆ B) ⋆ C) ⋆ D) ≅ Prod₄ A B C D

      -- ⊑ laws
      transportl : ∀ {A B C : Ty} → A ≅ B → A ⊑ C → B ⊑ C
      transportr : ∀ {A B C : Ty} → A ≅ B → C ⊑ A → C ⊑ B
      ＋⊑l : ∀ {A B C : Ty} → A ⊑ B → (A ＋ C) ⊑ (B ＋ C)
      ⋆⊑l : ∀ {A B C : Ty} → A ⊑ B → (A ⋆ C) ⊑ (B ⋆ C)
      ＋extendl : ∀ {A B : Ty} → A ⊑ (A ＋ B)

    ＋idr : ∀ {A : Ty} → (A ＋ 𝟘) ≅ A
    ＋idr = trans≅ ＋comm ＋idl
    ⋆idr : ∀ {A : Ty} → (A ⋆ 𝟙) ≅ A
    ⋆idr = trans≅ ⋆comm ⋆idl
    ⋆absorbr : ∀ {A : Ty} → (A ⋆ 𝟘) ≅ 𝟘
    ⋆absorbr = trans≅ ⋆comm ⋆absorbl
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

