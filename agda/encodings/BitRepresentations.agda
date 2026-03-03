{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --erasure #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

open import Data.Maybe
open import Data.Vec
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Descriptions

module BitRepresentations where

variable
  A B : Set
  a a' : A
  b b' : B
  t𝒟 : TaggedDescription
  n m : Nat

data Bit : Set where
  O : Bit
  I : Bit

𝔹_ : (n : Nat) → Set
𝔹 n = Vec Bit n

Chunks : Nat → Set
Chunks = Vec Nat

total : Chunks n → Nat
total [] = 0
total (x ∷ xs) = x + (total xs)

variable
  cs cs' : Chunks _

{-
-- BitRep cs 𝒟
-- The Chunks n represent the individual sizes of each "chunk"
-- of data described by 𝒟 in order
-- Useful for eliminating BitRep by peeling of a "chunk" of
-- a representation, usually also eliminating 𝒟 as well
-}
data BitRep : Chunks n → Description → Set₁ where
  ϵ : BitRep [] ⊤'
  box : (ptrSize : Nat) → BitRep cs 𝒟 →
        BitRep (ptrSize ∷ cs) (ind× 𝒟)
  ptr : (ptrSize : Nat) → BitRep cs 𝒟 →
        BitRep (ptrSize ∷ []) 𝒟
  -- TODO: 𝒟' should be the entire description, so need to keep track of context?
  unbox : BitRep cs 𝒟' → BitRep cs' 𝒟 →
          BitRep (cs ++ cs') (ind× 𝒟)
  case : {𝓓 : A → Description} →
         -- Provide a way to recover original a (without explicitly using the index)
         (rec : ∀ (@0 a : A) → BitRep cs (𝓓 a) → Maybe A) →
         -- Ensure that the recovery restores the original a  in the chosen sub-representation (usually definitionally by rec)
         ((a : A) → Σ (BitRep cs (𝓓 a))
                      (λ rep → rec a rep ≡ just a)) →
         BitRep cs (Σ' (A , 𝓓))
  prefix : (𝕓 : 𝔹 n) → BitRep cs 𝒟 → BitRep (n ∷ cs) 𝒟

record Repr (n : Nat) (A : Set) : Set where
  constructor repr
  field
    enc : A → 𝔹 n
    dec : 𝔹 n → Maybe A
  
    enc-dec-η : dec (enc a) ≡ just a
    dec-enc-η : ∀ {𝕓 : 𝔹 n} →
                Data.Maybe.map enc (dec 𝕓) ≡ just 𝕓

{-
-- Given a binary encoding/decoding of A, pack it at the head
-- of the rest of the representation
-}
pack : ∀ {A} {𝓓 : A → Description} →
       Repr n A →
       ((a : A) → BitRep cs (𝓓 a)) →
       BitRep (n ∷ cs) (Σ' (A , 𝓓))
pack {n = n} {A = A} {𝓓 = 𝓓} 
     (repr enc dec enc-dec-η _) reps =
  case rec (λ a → (prefix (enc a) (reps a) , enc-dec-η))
  where
    rec : ∀ (@0 a : A) → BitRep (n ∷ cs) (𝓓 a) → Maybe A
    -- TODO: unification error on indices here...
    rec _ (prefix 𝕓 _) = dec 𝕓
    rec _ _ = nothing

