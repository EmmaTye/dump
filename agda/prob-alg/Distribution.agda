open import Level using (Level)
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Nat as ℕ 
  using (ℕ)
open import Data.Product
open import Data.Rational as ℚ 
  using (ℚ; 0ℚ; 1ℚ)
open import Relation.Unary
  using (Pred)

module Distribution where

private
  variable
    ℓ o : Level
    m n : ℕ
    p q : ℚ
    i j : Fin _

data 𝒟' : (size : ℕ) → (sum : ℚ) → Set where
  ϵ : 𝒟' 0 0ℚ
  cons : (p : ℚ) → .⦃ ℚ.NonNegative p ⦄ → 𝒟' n q
         → 𝒟' (ℕ.suc n) (p ℚ.+ q)

-- Finite probability distribution
𝒟 : (n : ℕ) → Set
𝒟 n = 𝒟' n 1ℚ

-- Lookup
_[_] : (𝒹' : 𝒟' n p) (i : Fin n) → ℚ
cons q 𝒹' [ 0F ] = q
cons q 𝒹' [ suc i ] = 𝒹' [ i ]

module All where

  private
    variable
      𝒹' : 𝒟' _ _
      𝒹 : 𝒟 _

  liftP : (P : Pred (ℚ × Fin (ℕ.suc n)) ℓ) → Pred (ℚ × Fin n) ℓ
  liftP P (q , i) = P (q ,′ suc i)

  -- Indexed All predicates over distributions
  -- Allows definition of morphisms of FinProbSets
  data AllI {ℓ : Level} : (P : Pred (ℚ × Fin n) ℓ) → 𝒟' n q
                          → Set (Level.suc ℓ) where
    ϵ : {P : Pred (ℚ × Fin 0) _} → AllI P ϵ
    cons : {P : Pred (ℚ × Fin (ℕ.suc n)) ℓ} 
           → .⦃ _ : ℚ.NonNegative q ⦄
           → (x : P (q ,′ 0F)) → (xs : AllI {ℓ} (liftP P) 𝒹')
           → AllI P (cons q 𝒹')

