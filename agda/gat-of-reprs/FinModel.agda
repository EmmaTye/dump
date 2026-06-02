open Agda.Primitive

open import Data.Empty
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Fin.Properties
open import Data.Maybe
open import Data.Nat as ℕ
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Sum.Properties
open import Data.Unit
open import Data.Vec
  using (Vec; foldr′)
open import Function.Base
  using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; inspect; [_])

open import BaseTT
open import FinTT

module FinModel where
 
  private
    variable
      A B C D : Set
      a a' : A
      b b' : B
      c c' : C
      d d' : D
      i j : Fin _
      n m : ℕ

  module FinTypes where

    open FinTy ⦃ ... ⦄

    Ty : Set₁
    Ty = Σ[ A ∈ Set ] (Σ[ size ∈ ℕ ] (FinTy A size))

    Tm : Ty → Set
    Tm (A , _) = A

    instance
      ⊥ᶠ : FinTy ⊥ 0
      toTy ⦃ ⊥ᶠ ⦄ ()
      toFin ⦃ ⊥ᶠ ⦄ ()
      fin→ty ⦃ ⊥ᶠ ⦄ ()
      ty→fin ⦃ ⊥ᶠ ⦄ ()

    𝟘 : Ty
    𝟘 = (⊥ , (0 , ⊥ᶠ))

    instance
      ⊤ᶠ : FinTy ⊤ 1
      toTy ⦃ ⊤ᶠ ⦄ 0F = tt
      toFin ⦃ ⊤ᶠ ⦄ tt = 0F
      fin→ty ⦃ ⊤ᶠ ⦄ 0F = refl
      ty→fin ⦃ ⊤ᶠ ⦄ tt = refl

    𝟙 : Ty
    𝟙 = (⊤ , (1 , ⊤ᶠ))

    instance
      ⊎ᶠ : ∀ {n m : ℕ} ⦃ Aᶠ : FinTy A n ⦄ ⦃ Bᶠ : FinTy B m ⦄ →
            FinTy (A ⊎ B) (n ℕ.+ m)
      ⊎ᶠ {A} {B} {n = n} {m = m} ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = record {
          toTy = toTy⊎;
          toFin = toFin⊎;
          fin→ty = fin→ty⊎;
          ty→fin = ty→fin⊎
        }
        where
          toTy⊎ : Fin (n ℕ.+ m) → A ⊎ B
          toTy⊎ i with splitAt n i
          ... | inj₁ iᵃ = inj₁ (toTy iᵃ)
          ... | inj₂ iᵇ = inj₂ (toTy iᵇ)

          toFin⊎ : A ⊎ B → Fin (n ℕ.+ m)
          toFin⊎ (inj₁ a) = (toFin a) ↑ˡ m
          toFin⊎ (inj₂ b) = n ↑ʳ (toFin b)

          splitAt-toFin-inj₁ : ∀ {i} {a} → (toTy⊎ i ≡ inj₁ a) →
                      splitAt n i ≡ inj₁ (toFin a)
          splitAt-toFin-inj₁ {i} eq with splitAt n i
          ... | inj₁ iᵃ =
              cong inj₁ (trans
                          (sym (fin→ty ⦃ Aᶠ ⦄ iᵃ))
                          (cong (toFin ⦃ Aᶠ ⦄)
                                (inj₁-injective eq)))

          splitAt-toFin-inj₂ : ∀ {i} {b} → (toTy⊎ i ≡ inj₂ b) →
                      splitAt n i ≡ inj₂ (toFin b)
          splitAt-toFin-inj₂ {i} eq with splitAt n i
          ... | inj₂ iᵇ =
              cong inj₂ (trans
                          (sym (fin→ty ⦃ Bᶠ ⦄ iᵇ))
                          (cong (toFin ⦃ Bᶠ ⦄)
                                (inj₂-injective eq)))

          fin→ty⊎ : (i : Fin (n ℕ.+ m)) → toFin⊎ (toTy⊎ i) ≡ i
          fin→ty⊎ i with toTy⊎ i | inspect toTy⊎ i
          ... | inj₁ a | [ eq ] =
            splitAt⁻¹-↑ˡ (splitAt-toFin-inj₁ eq)
          ... | inj₂ b | [ eq ] =
            splitAt⁻¹-↑ʳ (splitAt-toFin-inj₂ eq)

          ty→fin⊎ : (ab : A ⊎ B) → toTy⊎ (toFin⊎ ab) ≡ ab
          ty→fin⊎ (inj₁ a) with splitAt n (toFin⊎ (inj₁ a))
                           | splitAt-↑ˡ n (toFin ⦃ Aᶠ ⦄ a) m
          ... | inj₁ iᵃ | eq =
            cong inj₁ (trans (cong (toTy ⦃ Aᶠ ⦄)
                                   (inj₁-injective eq))
                             (ty→fin ⦃ Aᶠ ⦄ a))

          ty→fin⊎ (inj₂ b) with splitAt n (toFin⊎ (inj₂ b))
                           | splitAt-↑ʳ n m (toFin ⦃ Bᶠ ⦄ b)
          ... | inj₂ iᵇ | eq =
            cong inj₂ (trans (cong (toTy ⦃ Bᶠ ⦄)
                                   (inj₂-injective eq))
                             (ty→fin ⦃ Bᶠ ⦄ b))

    _＋_ : Ty → Ty → Ty
    (A , (n , Aᶠ)) ＋ (B , (m , Bᶠ)) =
      ((A ⊎ B) , (n ℕ.+ m , ⊎ᶠ ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄))

    instance
      ×ᶠ : ∀ {n m : ℕ} ⦃ Aᶠ : FinTy A n ⦄ ⦃ Bᶠ : FinTy B m ⦄ →
            FinTy (A × B) (n ℕ.* m)
      ×ᶠ {A} {B} {n} {m} ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = record {
          toTy = toTy×;
          toFin = toFin×;
          fin→ty = fin→ty×;
          ty→fin = ty→fin×
        }
        where
          toTy× : Fin (n ℕ.* m) → A × B
          toTy× i with remQuot m i
          ... | iᵃ , iᵇ = toTy ⦃ Aᶠ ⦄ iᵃ ,′ toTy ⦃ Bᶠ ⦄ iᵇ

          toFin× : A × B → Fin (n ℕ.* m)
          toFin× (a , b) = combine (toFin ⦃ Aᶠ ⦄ a)
                                   (toFin ⦃ Bᶠ ⦄ b)

          fin→ty× : (i : Fin (n ℕ.* m)) → toFin× (toTy× i) ≡ i
          fin→ty× i =
            let
              iᵃ = (quotRem m i .proj₂)
              iᵇ = (quotRem {n} m i .proj₁)
            in
            trans
              (cong₂ combine (fin→ty ⦃ Aᶠ ⦄ iᵃ)
                             (fin→ty ⦃ Bᶠ ⦄ iᵇ))
              (combine-remQuot {n} m i)

          ty→fin× : (ab : A × B) → toTy× (toFin× ab) ≡ ab
          ty→fin× (a , b) =
            let
              remQuot-combine× =
                remQuot-combine (toFin ⦃ Aᶠ ⦄ a)
                                (toFin ⦃ Bᶠ ⦄ b)
            in
            cong₂ _,_
              (trans
                (cong (toTy ⦃ Aᶠ ⦄ ∘ proj₁) remQuot-combine×)
                (ty→fin ⦃ Aᶠ ⦄ a))
              (trans
                (cong (toTy ⦃ Bᶠ ⦄ ∘ proj₂) remQuot-combine×)
                (ty→fin ⦃ Bᶠ ⦄ b))

    _⋆_ : Ty → Ty → Ty
    (A , (n , Aᶠ)) ⋆ (B , (m , Bᶠ)) =
      ((A × B) , (n ℕ.* m , ×ᶠ ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄))

    -- TODO: define finite sum and prod types
    postulate
      Sum : ∀ {n} → Vec Ty n → Ty
      Prod : ∀ {n} → Vec Ty n → Ty

  instance
    FinTys : BaseTypes
    FinTys = record {FinTypes}

  module PartialIsos where
    open FinTypes
    record _≅_ (A B : Ty) : Set where
      field
        ⇒ : Tm A → Tm B
        _⇐ : Tm B → Tm A
        idl : ∀ {a : Tm A} →
              (⇒ a) ⇐ ≡ a
        idr : ∀ {b : Tm B} →
              ⇒ (b ⇐) ≡ b

    record _⊑_ (A B : Ty) : Set where
      field
        ⇒ : Tm A → Tm B
        _⇐ : Tm B → Maybe (Tm A)
        idl : ∀ {a : Tm A} →
              (⇒ a) ⇐ ≡ just a
        idr : ∀ {a : Tm A} {b : Tm B} →
              (b ⇐) ≡ just a →
              ⇒ a ≡ b

    -- TODO: copy proofs from PoCModel
    postulate
      refl≅ : ∀ {A : Ty} → A ≅ A
      sym≅ : ∀ {A B : Ty} → A ≅ B → B ≅ A
      trans≅ : ∀ {A B C : Ty} →
               A ≅ B → B ≅ C → A ≅ C

      refl⊑ : ∀ {A : Ty} → A ⊑ A
      trans⊑ : ∀ {A B C : Ty} →
               A ⊑ B → B ⊑ C → A ⊑ C

  instance
    PI : PartialIso FinTypes.Ty
    PI = record {PartialIsos}

  module FinModel where
    open FinTypes
    open PartialIsos

    -- TODO: copy proofs from PoCModel
    postulate
      ＋idl : ∀ {A : Ty} → (𝟘 ＋ A) ≅ A
      ＋comm : ∀ {A B : Ty} → (A ＋ B) ≅ (B ＋ A)
      ＋ass : ∀ {A B C : Ty} → ((A ＋ B) ＋ C) ≅ (A ＋ (B ＋ C))
      ⋆idl : ∀ {A : Ty} → (𝟙 ⋆ A) ≅ A
      ⋆comm : ∀ {A B : Ty} → (A ⋆ B) ≅ (B ⋆ A)
      ⋆ass : ∀ {A B C : Ty} → ((A ⋆ B) ⋆ C) ≅ (A ⋆ (B ⋆ C))
      ⋆absorbl : ∀ {A : Ty} → (𝟘 ⋆ A) ≅ 𝟘
      ⋆＋dist : ∀ {A B C : Ty} →
                (A ⋆ (B ＋ C)) ≅ ((A ⋆ B) ＋ (A ⋆ C))

      ＋Sum : ∀ {n} {As : Vec Ty n} → Sum As ≅ foldr′ _＋_ 𝟘 As
      ⋆Prod : ∀ {n} {As : Vec Ty n} → Prod As ≅ foldr′ _⋆_ 𝟙 As

      ＋≅l : ∀ {A B C : Ty} → A ≅ B → (A ＋ C) ≅ (B ＋ C)
      ⋆≅l : ∀ {A B C : Ty} → A ≅ B → (A ⋆ C) ≅ (B ⋆ C)

      transportl : ∀ {A B C : Ty} → A ≅ B → A ⊑ C → B ⊑ C
      transportr : ∀ {A B C : Ty} → A ≅ B → C ⊑ A → C ⊑ B
      ＋⊑l : ∀ {A B C : Ty} → A ⊑ B → (A ＋ C) ⊑ (B ＋ C)
      ⋆⊑l : ∀ {A B C : Ty} → A ⊑ B → (A ⋆ C) ⊑ (B ⋆ C)
      ＋extendl : ∀ {A B : Ty} → A ⊑ (A ＋ B)
      𝟘⊑𝟙 : 𝟘 ⊑ 𝟙

-- TODO: fix UnsolvedConstraints
--  instance
--    FinModel : BaseTT {lzero}
--    FinModel = record {FinModel}

  postulate
    instance
      FinModel : BaseTT {lzero}

