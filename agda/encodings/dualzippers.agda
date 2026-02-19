
module dualzippers where

open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat using (Nat; _-_)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Nat using (_<_; ℕ; _≤_; zero; suc)
open import Data.Vec using (Vec; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

coerce : {A B : Set} → A ≡ B → A → B
coerce refl a = a

record 𝔹zipperObj (size : ℕ) (i : Fin size) : Set where
  constructor zip
  field
    prefix : Vec Bool (toℕ i) -- reverse indices
    focus : Bool
    suffix : Vec Bool (size - (toℕ i) - 1)

variable
  size : ℕ
  i : Fin _
  𝕓 : 𝔹zipperObj _ _

-- where the real magic happens: if you go left in the data
-- structure, how far left do you need to go in the bit array?
record 𝔹indices : Set where
  field
    leftIndex : 𝔹zipperObj size i → Fin size
    rightIndex : 𝔹zipperObj size i → Fin size

record 𝔹zipper (inds : 𝔹indices) : Set where
  open 𝔹indices inds
  field
    left : (𝕓 : 𝔹zipperObj size i) → 
           𝔹zipperObj size (leftIndex 𝕓)
    right : (𝕓 : 𝔹zipperObj size i) → 
            𝔹zipperObj size (rightIndex 𝕓)

    left-right-index-id : ∀ (𝕓 : 𝔹zipperObj size i) →
      (rightIndex (left 𝕓) ≡ i)
    left-right-id : ∀ {𝕓 : 𝔹zipperObj size i} → 
      right (left 𝕓) ≡ coerce (cong (𝔹zipperObj size) 
                                (sym (left-right-index-id 𝕓)))
                       𝕓

    right-left-index-id : ∀ (𝕓 : 𝔹zipperObj size i) →
      (leftIndex (right 𝕓) ≡ i)
    right-left-id : ∀ {𝕓 : 𝔹zipperObj size i} → 
      left (right 𝕓) ≡ coerce (cong (𝔹zipperObj size) 
                                (sym (right-left-index-id 𝕓)))
                       𝕓

pad : ∀ {size} {i : Fin size} (target : Nat) → 
      (size ≤ target) → 
      𝔹zipperObj size i →
      𝔹zipperObj target _
-- pad {size} {i} target sizePf (zip pre b suf) = 
--   zip (replicate (target - size) false ++ pre) b 
--     (coerce (cong (Vec Bool) ?) suf)

record ReprZipper (A : Set) (size : ℕ) : Set where
  field
    left : A → A
    right : A → A
    focusIndex : A → Fin size
    enc : (a : A) → 𝔹zipperObj size (focusIndex a)
    dec : 𝔹zipperObj size i → Maybe A

    left-right-id : ∀ {a : A} → right (left a) ≡ a
    right-left-id : ∀ {a : A} → left (right a) ≡ a

