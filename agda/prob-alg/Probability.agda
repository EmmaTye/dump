open import Level

open import Data.Nat as ℕ
  using (ℕ)
open import Data.Nat.Coprimality
  using (Coprime; coprime-/gcd)
open import Data.Nat.DivMod
open import Data.Nat.GCD
open import Data.Nat.Properties
open import Data.Sum using (inj₂)
open import Function.Base
  using (_$_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality

module Probability where

-- Syntax copied from Data.Rational.Base

-- A fraction less than 1
-- Constructed from a numerator and how much larger the denominator is than it
record Prob : Set where
  constructor mkProb
  field
    numerator : ℕ
    denominator-diff : ℕ
    .isCoprime : Coprime numerator (denominator-diff ℕ.+ numerator)
    dNonZero : ℕ.NonZero (denominator-diff ℕ.+ numerator)

  denominator : ℕ
  denominator = numerator ℕ.+ denominator-diff
  
  instance
    d≢0 : ℕ.NonZero denominator
    d≢0 rewrite (+-comm numerator denominator-diff) = dNonZero


open Prob public using (d≢0)
  renaming
  ( numerator    to ↥_
  ; denominator  to ↧_
  )

infix 4 _≤_ _<_ _≥_ _>_

data _≤_ : Rel Prob 0ℓ where
  *≤* : ∀ {p q} → (↥ p ℕ.* ↧ q) ℕ.≤ (↥ q ℕ.* ↧ p) → p ≤ q

data _<_ : Rel Prob 0ℓ where
  *<* : ∀ {p q} → (↥ p ℕ.* ↧ q) ℕ.< (↥ q ℕ.* ↧ p) → p < q

_≥_ : Rel Prob 0ℓ
x ≥ y = y ≤ x

_>_ : Rel Prob 0ℓ
x > y = y < x

-- Construct a probability from any numerator and denominator, given the denominator is non-zero and larger
normalise : ∀ (m n : ℕ) → m ℕ.≤ n
            → .⦃ _ : ℕ.NonZero n ⦄
            → Prob
normalise m n m≤n =
  mkProb num denom-diff isCoprime isNonZero
  where
    instance
      g≢0 = ℕ.≢-nonZero (gcd[m,n]≢0 m n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
    num = m ℕ./ gcd m n
    denom-diff = (n ℕ./ gcd m n) ℕ.∸ num
    num≤denom = /-monoˡ-≤ (gcd m n) m≤n

    isCoprime : Coprime num (denom-diff ℕ.+ num)
    isCoprime rewrite (m∸n+n≡m num≤denom) = coprime-/gcd m n

    isNonZero : ℕ.NonZero (denom-diff ℕ.+ num)
    isNonZero rewrite (m∸n+n≡m num≤denom) = 
      ℕ.>-nonZero (m≥n⇒m/n>0 (gcd[m,n]≤n m n))

-- Smart constructor for unitary fractions
1/_ : (d : ℕ) → .⦃ _ : ℕ.NonZero d ⦄ → Prob
1/ (ℕ.suc d⁻) = normalise 1 (ℕ.suc d⁻) (ℕ.s≤s ℕ.z≤n)

0p : Prob
0p = normalise 0 1 ℕ.z≤n

1p : Prob
1p = 1/ 1

half : Prob
half = 1/ 2

infixl 7 _*_ _⊓_
infixl 6 _-_ _+_ _⊔_

add' : (p q : Prob) → Prob
add' p@record{} q@record{}  = 
  normalise n d n≤d
  where
    instance
      d*≢0 : ℕ.NonZero (↧ p ℕ.* ↧ q)
      d*≢0 = m*n≢0 (↧ p) (↧ q) ⦃ d≢0 p ⦄ ⦃ d≢0 q ⦄
    n = ↥ p ℕ.* ↧ q ℕ.+ ↥ q ℕ.* ↧ p
    d = ↧ p ℕ.* ↧ q

    n≤d : n ℕ.≤ d
    n≤d = {!!}

--_*_ : Prob → Prob → Prob
--p@record{} * q@record{} = normalise (↥ p ℕ.* ↥ q) (↧ p ℕ.* ↧ q) _
--
--_-_ : Prob → Prob → Prob
