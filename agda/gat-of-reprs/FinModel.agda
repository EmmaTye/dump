open import Data.Empty
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Fin.Properties
open import Data.Nat as ℕ
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Sum.Properties
open import Data.Unit
open import Function.Base
  using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; inspect; [_])

open import PoCModel
open import BaseTT
open import FinTT
  renaming (_∘_ to _∘′_)
open import FunTT

module FinModel where
 
  private
    variable
      A B C D : Set
      a a' : A
      b b' : B
      c c' : C
      d d' : D
      i j : Fin _

  open FinTy ⦃ ... ⦄

  instance
    ⊥ᶠ : FinTy ⊥
    size ⦃ ⊥ᶠ ⦄ = 0
    toTy ⦃ ⊥ᶠ ⦄ ()
    toFin ⦃ ⊥ᶠ ⦄ ()
    fin→ty ⦃ ⊥ᶠ ⦄ ()
    ty→fin ⦃ ⊥ᶠ ⦄ ()

  instance
    ⊤ᶠ : FinTy ⊤
    size ⦃ ⊤ᶠ ⦄ = 1
    toTy ⦃ ⊤ᶠ ⦄ 0F = tt
    toFin ⦃ ⊤ᶠ ⦄ tt = 0F
    fin→ty ⦃ ⊤ᶠ ⦄ 0F = refl
    ty→fin ⦃ ⊤ᶠ ⦄ tt = refl

  instance
    ⊎ᶠ : ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄ →
          FinTy (A ⊎ B)
    ⊎ᶠ {A} {B} ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = record {
        size = size⊎;
        toTy = toTy⊎;
        toFin = toFin⊎;
        fin→ty = fin→ty⊎;
        ty→fin = ty→fin⊎
      }
      where
        size⊎ = size ⦃ Aᶠ ⦄ ℕ.+ size ⦃ Bᶠ ⦄

        toTy⊎ : Fin size⊎ → A ⊎ B
        toTy⊎ i with splitAt (size ⦃ Aᶠ ⦄) i
        ... | inj₁ iᵃ = inj₁ (toTy iᵃ)
        ... | inj₂ iᵇ = inj₂ (toTy iᵇ)

        toFin⊎ : A ⊎ B → Fin size⊎
        toFin⊎ (inj₁ a) = (toFin a) ↑ˡ (size ⦃ Bᶠ ⦄)
        toFin⊎ (inj₂ b) = (size ⦃ Aᶠ ⦄) ↑ʳ (toFin b)

        splitAt-toFin-inj₁ : ∀ {i} {a} → (toTy⊎ i ≡ inj₁ a) →
                    splitAt (size ⦃ Aᶠ ⦄) i ≡ inj₁ (toFin a)
        splitAt-toFin-inj₁ {i} eq with splitAt (size ⦃ Aᶠ ⦄) i
        ... | inj₁ iᵃ =
            cong inj₁ (trans
                        (sym (fin→ty ⦃ Aᶠ ⦄ iᵃ))
                        (cong (toFin ⦃ Aᶠ ⦄)
                              (inj₁-injective eq)))

        splitAt-toFin-inj₂ : ∀ {i} {b} → (toTy⊎ i ≡ inj₂ b) →
                    splitAt (size ⦃ Aᶠ ⦄) i ≡ inj₂ (toFin b)
        splitAt-toFin-inj₂ {i} eq with splitAt (size ⦃ Aᶠ ⦄) i
        ... | inj₂ iᵇ =
            cong inj₂ (trans
                        (sym (fin→ty ⦃ Bᶠ ⦄ iᵇ))
                        (cong (toFin ⦃ Bᶠ ⦄)
                              (inj₂-injective eq)))

        fin→ty⊎ : (i : Fin size⊎) → toFin⊎ (toTy⊎ i) ≡ i
        fin→ty⊎ i with toTy⊎ i | inspect toTy⊎ i
        ... | inj₁ a | [ eq ] =
          splitAt⁻¹-↑ˡ (splitAt-toFin-inj₁ eq)
        ... | inj₂ b | [ eq ] =
          splitAt⁻¹-↑ʳ (splitAt-toFin-inj₂ eq)

        ty→fin⊎ : (ab : A ⊎ B) → toTy⊎ (toFin⊎ ab) ≡ ab
        ty→fin⊎ (inj₁ a) with splitAt (size ⦃ Aᶠ ⦄)
                                      (toFin⊎ (inj₁ a))
                         | splitAt-↑ˡ (size ⦃ Aᶠ ⦄)
                                      (toFin ⦃ Aᶠ ⦄ a)
                                      (size ⦃ Bᶠ ⦄)
        ... | inj₁ iᵃ | eq =
          cong inj₁ (trans (cong (toTy ⦃ Aᶠ ⦄)
                                 (inj₁-injective eq))
                           (ty→fin ⦃ Aᶠ ⦄ a))

        ty→fin⊎ (inj₂ b) with splitAt (size ⦃ Aᶠ ⦄)
                                      (toFin⊎ (inj₂ b))
                         | splitAt-↑ʳ (size ⦃ Aᶠ ⦄)
                                      (size ⦃ Bᶠ ⦄)
                                      (toFin ⦃ Bᶠ ⦄ b)
        ... | inj₂ iᵇ | eq =
          cong inj₂ (trans (cong (toTy ⦃ Bᶠ ⦄)
                                 (inj₂-injective eq))
                           (ty→fin ⦃ Bᶠ ⦄ b))

  instance
    ×ᶠ : ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄ →
          FinTy (A × B)
    ×ᶠ {A} {B} ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = record {
        size = size×;
        toTy = toTy×;
        toFin = toFin×;
        fin→ty = fin→ty×;
        ty→fin = ty→fin×
      }
      where
        size× = size ⦃ Aᶠ ⦄ ℕ.* size ⦃ Bᶠ ⦄

        toTy× : Fin size× → A × B
        toTy× i with remQuot (size ⦃ Bᶠ ⦄) i
        ... | iᵃ , iᵇ = toTy ⦃ Aᶠ ⦄ iᵃ ,′ toTy ⦃ Bᶠ ⦄ iᵇ

        toFin× : A × B → Fin size×
        toFin× (a , b) = combine (toFin ⦃ Aᶠ ⦄ a)
                                 (toFin ⦃ Bᶠ ⦄ b)

        fin→ty× : (i : Fin size×) → toFin× (toTy× i) ≡ i
        fin→ty× i =
          let
            iᵃ = (quotRem (size ⦃ Bᶠ ⦄) i .proj₂)
            iᵇ = (quotRem {size ⦃ Aᶠ ⦄} (size ⦃ Bᶠ ⦄) i .proj₁)
          in
          trans 
            (cong₂ combine (fin→ty ⦃ Aᶠ ⦄ iᵃ) 
                           (fin→ty ⦃ Bᶠ ⦄ iᵇ))
            (combine-remQuot {size ⦃ Aᶠ ⦄} (size ⦃ Bᶠ ⦄) i)

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

