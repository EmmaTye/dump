open import Level as L
  using (Level)
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Nat as ℕ 
  using (ℕ)
open import Data.Product
open import Data.Rational as ℚ 
  using (ℚ; 0ℚ; 1ℚ)
open import Relation.Binary.Core
  using (Rel)
open import Relation.Binary.PropositionalEquality

open import Categories.Category

open import Distribution
open import FinSet

module FinProbSet where

private
  variable
    ℓ o : Level

open FinSetObj
open Category FinSet

FinProbSetObj : Set₁
FinProbSetObj = Σ[ Aᶠ ∈ Obj ] 𝒟 (Aᶠ .size)

FinProbSetMorph : Rel FinProbSetObj _
FinProbSetMorph (Aᶠ , dᴬ) (Bᶠ , dᴮ) =
  Subset (Aᶠ ⇒ Bᶠ)
         (λ f → All.AllI (P f) dᴮ)
  where
    P : (f : Aᶠ ⇒ Bᶠ) → ℚ × Fin (Bᶠ .size) → Set _
    P f (q , iᴮ) = q ≡ {!!}
      -- TODO: need to prove this creates a valid
      -- probability (i.e. 0 ≤ x ≤ 1)
      -- Probably need some lemmas in Distribution, like
      -- filtered sums add up to less than sum etc.
      -- List.fold (λ iᴬ sum → dᴬ [ iᴬ ] ℚ.+ sum)
      --   (List.findIndicesᵇ f (=ᵇ iᴮ))
      --   0ℚ

FinProbSet : Category _ _ _
FinProbSet = record
  { Obj = FinProbSetObj
  ; _⇒_ = FinProbSetMorph
  ; _≈_ = {!!} -- TODO: use FinSet._≈_ on 1st proj, ignore snd(should anyway since snd is irrelevant)
  ; id = {!!}
  ; _∘_ = {!!}
  ; assoc = {!!}
  ; sym-assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; identity² = {!!}
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  }

