open Agda.Primitive

open import BaseTT

module FunTT where

  private
    variable
      𝓁 : Level

  open BaseTypes ⦃ ... ⦄
  open PartialIso ⦃ ... ⦄

  record FunTT {𝓁} : Set (lsuc (lsuc 𝓁)) where

    field
      ⦃ BTT ⦄ : BaseTT {𝓁}
      _⇛_ : Ty → Ty → Ty

      𝟘⇛a : ∀ {A : Ty} → (𝟘 ⇛ A) ≅ 𝟙
      -- If A is non-empty, then A ⇛ 𝟘 ≅ 𝟘
      -- Prevents deriving 𝟘 ≅ 𝟙
      a⇛𝟘 : ∀ {A : Ty} → Tm A → (A ⇛ 𝟘) ≅ 𝟘

      𝟙⇛a : ∀ {A : Ty} → (𝟙 ⇛ A) ≅ A
      a⇛𝟙 : ∀ {A : Ty} → (A ⇛ 𝟙) ≅ 𝟙

      ＋⋆⇛ : ∀ {A B C : Ty} → 
             ((A ＋ B) ⇛ C) ≅ ((A ⇛ C) ⋆ (B ⇛ C))
      ⋆⇛ : ∀ {A B C : Ty} →
           (A ⇛ (B ⋆ C)) ≅ ((A ⇛ B) ⋆ (A ⇛ C))
      curry : ∀ {A B C : Ty} →
              ((A ⋆ B) ⇛ C) ≅ (A ⇛ (B ⇛ C))

      -- ≅ and ⇛ laws
      ⇛≅contra : ∀ {A B C : Ty} →
                 A ≅ B →
                 (A ⇛ C) ≅ (B ⇛ C)
      ⇛≅cov : ∀ {A B C : Ty} →
              B ≅ C →
              (A ⇛ B) ≅ (A ⇛ C)

      -- ⊑ and ⇛ laws
      ⇛⊑contra : ∀ {A B C : Ty} →
                 B ⊑ A →
                 (A ⇛ C) ⊑ (B ⇛ C)
      ⇛⊑cov : ∀ {A B C : Ty} →
              B ⊑ C →
              (A ⇛ B) ⊑ (A ⇛ C)

    ⇛swap : ∀ {A B C D : Ty} →
            B ⊑ A → C ⊑ D →
            (A ⇛ C) ⊑ (B ⇛ D)
    ⇛swap b⊑a c⊑d = trans⊑ (⇛⊑contra b⊑a) (⇛⊑cov c⊑d)

