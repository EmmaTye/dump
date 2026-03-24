open import Agda.Builtin.Sigma

open import Data.Bool
open import Data.Empty.Irrelevant
open import Data.Maybe
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Relation.Nullary

open import BitOperations
open UnknownNat
open import Descriptions

module BitRepresentations where

private
  variable
    n m : ℕ
    𝓃 𝓂  𝓃' 𝓂' : ℕₓ
    A B : Set
    a a' : A
    b b' : B
    𝒟 𝒟' : Description₀
    𝒟ᵃ : A → Description₀
    𝒟ᵇ : B → Description₀

module Core where

  mutual
    -- BitRep 𝓃 𝓂  𝒟 
    -- describes how to represent the description 𝒟 in a bit vector between the indices 𝓃 and 𝓂
    data BitRep : ℕₓ → ℕₓ → Description₀ → Set₁ where
      ϵ : BitRep 0χ 0χ ⊤'
      -- If we have an inductive case, then we can't know the final size of the representation, no matter what representation the rest of the description has
      box : BitRep 𝓃 𝓂  𝒟 →
            BitRep χ χ (ind× 𝒟)
      case : (cases : (a : A) → BitRep 𝓃 𝓂 (𝒟ᵃ a)) →
      -- TODO: Recover...
             BitRep 𝓃 𝓂 (Σ' (A , 𝒟ᵃ))
      -- We're working with little endian storage of bits, so the "prefix" will actually go at the end
      prefix : BitRep 𝓃 𝓂 𝒟 → 𝔹 𝓂' → BitRep 𝓃 (𝓂 ⊕ 𝓂') 𝒟
  
    -- Recover a startInd size pf rep
    -- describes how to recover the value a from size no. of bits, starting from startInd after 𝓃 (inclusive) of a bit representation rep
    data Recover (a : A) : (startInd : ℕ) → (size : ℕₓ) →
                           (Num startInd) ⊕ size ≤ₓ 𝓂 →
                           BitRep 𝓃 𝓂 𝒟 →
                           Set₁ where
      -- If the value is packed at the start of the representation, decode it (ensuring the decoding is correct)
      decodePre : {size : ℕₓ} {𝕓 : 𝔹 size}
                  {rep : BitRep 𝓃 𝓂 𝒟} →
                  (dec : 𝔹 size → Maybe A) →
                  (lePf : size ≤ₓ 𝓂) →
                  (dec 𝕓 ≡ just a) →
                  -- TODO: need to prove
                  -- size ≤ₓ 𝓂  → 0χ ⊕ size ≤ₓ size ⊕ 𝓂
                  Recover a 0 size ? (prefix rep 𝕓)
--      -- Allow the value to be packed inside another case split, as long as it can still be recovered at the same position in each
--       inspectCase : {startA : Nat}{endA : Nat}
--                     {cases : (b : B) → BitRep n (𝒟ᵇ b) 𝒟'}
--                     {startB : Nat} → {endB : Nat}
--                     {recB : (b : B) → Recover b startB endB
--                                               (cases b)} →
--                     ((b : B) → Recover a startA endA
--                                        (cases b)) →
--                     Recover a startA endA
--                             (case cases startB endB recB)
--       -- Allow the value to be packed after a prefix
--       skipPre : {startA : Nat} {endA : Nat}
--                 {rep : BitRep m 𝒟 𝒟'} {𝕓 : 𝔹 n} →
--                 Recover a startA endA rep →
--                 Recover a (startA + n) (endA + n)
--                         (prefix 𝕓 rep)
--       -- Allow the value to be packed after a boxed inductive pointer
--       skipBox : {startA : Nat} {endA : Nat}
--                 {rep : BitRep n 𝒟 𝒟'} {ptrSize : Nat} →
--                 Recover a startA endA rep →
--                 Recover a (startA + ptrSize) (endA + ptrSize)
--                         (box ptrSize rep)
--       -- Allow the value to be packed after an unboxed indutive instance
--       skipUnbox : {startA : Nat} {endA : Nat}
--                   {rep' : BitRep n 𝒟' 𝒟'}
--                   {rep : BitRep m 𝒟 𝒟'} →
--                   Recover a startA endA rep →
--                   Recover a (startA + n) (endA + n)
--                           (unbox rep' rep)
-- 
--   BitRepr : Set₁
--   BitRepr = (n : Nat) → (𝒟 : Description) → BitRep n 𝒟 𝒟

-- module Extra where
--   open Core
--   open Environments
-- 
--   record Repr (n : Nat) (A : Set) : Set where
--     constructor repr
--     field
--       enc : A → 𝔹 n
--       dec : 𝔹 n → Maybe A
--     
--       enc-dec-η : dec (enc a) ≡ just a
--       dec-enc-η : ∀ {𝕓 : 𝔹 n} →
--                   (p : Σ A (λ a → (dec 𝕓 ≡ just a))) →
--                   enc (fst p) ≡ 𝕓
-- 
--   bitSizeEn : En → Nat
--   bitSizeEn E = fst (bitSizeEn' E)
--     where
--       bitSizeEn' : En → Σ Nat (λ _ → En)
--       bitSizeEn' nE = (0 , nE)
--       bitSizeEn' (cE _ E) with (bitSizeEn' E)
--       ... | (bits , nE) = (suc bits , E)
--       ... | (bits , cE _ E') = (bits , E')
-- 
-- -- For an environment, provide a representation for its tags
--   encodeEn : (E : En) → Repr (bitSizeEn E) (# E)
--   encodeEn nE = repr (λ e → ⊥-elim (tagIndicesNot e))
--                      (λ [] → nothing)
--                      (λ {e : # nE} → ⊥-elim (tagIndicesNot e))
--                      (λ (e , _) → ⊥-elim (tagIndicesNot e))
--   encodeEn E@(cE _ E') with (encodeEn E')
--   ... | (repr enc' dec' η₁ η₂) = repr enc ? ? ?
--     where
--       enc : # E → 𝔹 (bitSizeEn E)
--       enc 𝟎 = pad O (bitSizeEn E) []
--       enc (𝟏+ e) with (enc' e)
--       ... | 𝕓 =
--         let
--           (overflow? , 𝕓) = addI 𝕓
--         in
--         if overflow?
--         then 𝕓 ++ [ I ]
--         else 𝕓
-- 
-- --  tagRepr : ∀ {E : En} → Repr (noBits (enSize E)) (# E)
-- --  tagRepr {E} = repr enc dec ? ?
-- --    where
-- --      enc : ∀ {E' : En} → # E' → 𝔹 (noBits (enSize E'))
-- --      enc {E'} 𝟎 = rep O (noBits (enSize E'))
-- --      enc {E'} (𝟏+ e) = ? -- add 1 bitwise to e
-- --  
-- --      dec : ∀ {E' : En} → 𝔹 (noBits (enSize E')) → Maybe (# E)
--   
--   {-
--   -- Given a binary encoding/decoding of A, pack it at the head
--   -- of the rest of the representation
--   -}
--   pack : ∀ {A} {𝒟ᵃ} →
--          Repr n A →
--          ((a : A) → BitRep m (𝒟ᵃ a) 𝒟) →
--          BitRep (n + m) (Σ' (A , 𝒟ᵃ)) 𝒟
--   pack {n = n} {m = m} {𝒟 = 𝒟} {A = A} {𝒟ᵃ = 𝒟ᵃ}
--        (repr enc dec enc-dec-η _) reps =
--     case cases 0 n rec
--     where
--       cases : (a : A) → BitRep (n + m) (𝒟ᵃ a) 𝒟
--       cases a = prefix (enc a) (reps a)
--   
--       rec : ∀ (a : A) → Recover a 0 n (cases a)
--       rec a = decodePre dec enc-dec-η

-- TODO:
-- - implement default Repr of tag environments
-- - implement collapseTagSums by iterating through a
--   description until there are no more Σ' (# E) ...
--   sub-descriptions, combine all #E's to create a new
--   environment, use default Repr of the new environment and
--   prefix it. Build up correct decoders for the each inter-
--   mediate tags as you go
-- - implement GMP-style integers by
--   - successive unbox calls until the int fits into the
--     given word size
--   - encode the integer in the word size
--   - then box and finish

