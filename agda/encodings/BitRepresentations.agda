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
  n m : Nat
  𝒟 𝒟' : Description
  𝒟ᵃ : A → Description
  𝒟ᵇ : B → Description

data Bit : Set where
  O : Bit
  I : Bit

𝔹_ : (n : Nat) → Set
𝔹 n = Vec Bit n

mutual
  data BitRep : Nat → Description → Set₁ where
    ϵ : BitRep 0 ⊤'
    box : (ptrSize : Nat) → BitRep n 𝒟 →
          BitRep (ptrSize + n) (ind× 𝒟)
    -- Point to another representation of 𝒟
    ptr : (ptrSize : Nat) → BitRep n 𝒟 →
          BitRep ptrSize 𝒟
    -- TODO: 𝒟' should be the entire description, so need to keep track of context?
    unbox : BitRep n 𝒟' → BitRep m 𝒟 →
            BitRep (n + m) (ind× 𝒟)
    case : (cases : (a : A) → BitRep n (𝒟ᵃ a)) →
           -- Provide a way to recover the original A from each case, starting the recovery at startA (inclusive) and ending the recovery at endA (exclusive)
           (startA : Nat) → (endA : Nat) →
           (∀ (a : A) → Recover a startA endA (cases a)) →
           BitRep n (Σ' (A , 𝒟ᵃ))
    prefix : (𝕓 : 𝔹 n) → BitRep m 𝒟 → BitRep (n + m) 𝒟

  -- Recover a startA endA rep
  -- describes how to recover the value a from the bits inside the interval from startA (inclusive) to endA (exclusive) of a bit representation rep
  data Recover (a : A) : (startA : Nat) → (endA : Nat) → BitRep n 𝒟 → Set₁ where
    -- If the value is packed at the start of the representation, decode it (ensuring the decoding is correct)
    decodePre : {sizeA : Nat} {𝕓 : 𝔹 sizeA} {rep : BitRep n 𝒟} → 
                (dec : 𝔹 sizeA → Maybe A) →
                (dec 𝕓 ≡ just a) →
                Recover a 0 sizeA (prefix 𝕓 rep)
   -- Allow the value to be packed inside another case split, as long as
    -- it can still be recovered at the same position in each
    inspectCase : {startA : Nat}{endA : Nat}
                  {cases : (b : B) → BitRep n (𝒟ᵇ b)}
                  {startB : Nat} → {endB : Nat}
                  {recoverB : (b : B) → Recover b startB endB (cases b)} →
                  ((b : B) → Recover a startA endA (cases b)) →
                  Recover a startA endA (case cases startB endB recoverB)
    -- Allow the value to be packed after a prefix
    skipPre : {startA : Nat} {endA : Nat} {rep : BitRep m 𝒟} {𝕓 : 𝔹 n} →
              Recover a startA endA rep →
              Recover a (startA + n) (endA + n) (prefix 𝕓 rep)
    -- Allow the value to be packed after a boxed inductive pointer
    skipBox : {startA : Nat} {endA : Nat} {rep : BitRep n 𝒟} {ptrSize : Nat} →
              Recover a startA endA rep →
              Recover a (startA + ptrSize) (endA + ptrSize) (box ptrSize rep)
    -- Allow the value to be packed after an unboxed indutive instance
    skipUnbox : {startA : Nat} {endA : Nat} {rep' : BitRep n 𝒟'} {rep : BitRep m 𝒟} →
                Recover a startA endA rep →
                Recover a (startA + n) (endA + n) (unbox rep' rep)

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
pack : ∀ {A} {𝒟ᵃ} →
       Repr n A →
       ((a : A) → BitRep m (𝒟ᵃ a)) →
       BitRep (n + m) (Σ' (A , 𝒟ᵃ))
pack {n = n} {m = m} {A = A} {𝒟ᵃ = 𝒟ᵃ}
     (repr enc dec enc-dec-η _) reps =
  case cases 0 n rec
  where
    cases : (a : A) → BitRep (n + m) (𝒟ᵃ a)
    cases a = prefix (enc a) (reps a)

    rec : ∀ (a : A) → Recover a 0 n (cases a)
    rec a = decodePre dec enc-dec-η

-- TODO:
-- - implement default Repr of tag environments
-- - implement collapseTagSums by iterating through a
--   description until there are no more Σ' (# E) ...
--   sub-descriptions, combine all #E's to create a new
--   environment, use default Repr of the new environment and
--   prefix it. Build up correct decoders for the each inter-
--   mediate tags as you go
-- - carry the entire contextual description for BitRep
--   through for the unbox constructor
-- - implement GMP-style integers by
--   - successive unbox calls until the int fits into the
--     given word size
--   - encode the interger in the word size
--   - then box and finish

