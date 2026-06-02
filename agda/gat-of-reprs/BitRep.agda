open Agda.Primitive
  hiding (_⊔_)

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
  hiding (map)
open import Data.Vec as Vec
  using (Vec; _∷_; []; map)
open import Function.Base
  using (id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst)

module BitRep where

  data BitOrByte : Set where
    Bit : BitOrByte
    Byte : BitOrByte

  private
    variable
      m n : ℕ
      tag tag₁ tag₂ : BitOrByte

  byte : ℕ
  byte = 2 ^ 8

  toByte : (tag : BitOrByte) → ℕ → ℕ
  toByte Bit n = 8 * n
  toByte Byte n = n

  -- Biased bit-representations
  -- Floating points can be represented by e.g.
  -- sign   exp    significant
  -- 𝔹[ 1 ] ++ 𝔹[ 8 ] ++ 𝔹[ 23 ] : BitRep Bit 32
  -- and unions by e.g.
  --  sum (  Int16 ∷   Int8  ⋆   Int8   ∷ [] )
  -- U[ 2 , 𝔹[ 2 ] ∷ (𝔹[ 1 ] ++ 𝔹[ 1 ]) ∷ [] ] : BitRep Byte 3
  data BitRep (tag : BitOrByte) : ℕ → Set where
    ϵ : BitRep tag 0
    𝔹[_] : (m : ℕ) → BitRep tag m
    _++_ : BitRep tag m → BitRep tag n → BitRep tag (m + n)
    -- Pack all choices into a single byte
    U[_,_,_] : (m : ℕ) → m ≤ byte → Vec (BitRep tag n) m → BitRep tag ((toByte tag 1) + n)

  module Tautologies where

    private
      variable
        𝕓 𝕓₁ 𝕓₂ 𝕓₃ : BitRep _ _

    -- Tautologies
    -- "Unbiasing" the representation
    data Taut : BitRep tag₁ m → BitRep tag₂ n → Set where
      -- left identity
      ϵ++𝔹[x]≡𝔹[x] : Taut {tag} {m} {tag} {m}
                          (ϵ ++ 𝔹[ m ]) 𝔹[ m ]
      -- right identity
      𝔹[x]++ϵ≡𝔹[x] : Taut {tag₁ = tag} {tag₂ = tag}
                          (𝔹[ m ] ++ ϵ) 𝔹[ m ]
      -- unique identity
      ϵ≡𝔹[0] : Taut {tag} {0} {tag} {0} 
                    ϵ 𝔹[ 0 ]
      -- append
      𝔹[x]++𝔹[y]≡𝔹[x+y] : Taut {tag₁ = tag} {tag₂ = tag} 
                               (𝔹[ m ] ++ 𝔹[ n ]) 𝔹[ m + n ]
      -- symmetric choices
      U[m,_,a∷b∷xs]≡U[m,_,b∷a∷xs] : 
        ∀ {xs : Vec (BitRep tag n) m}
          {pf : 2+ m ≤ byte} →
        Taut U[ 2+ m , pf , 𝕓₁ ∷ 𝕓₂ ∷ xs ]
             U[ 2+ m , pf , 𝕓₂ ∷ 𝕓₁ ∷ xs ]
      -- bit-to-byte
      𝔹[xByte]≡𝔹[8*xBit] : Taut {tag₁ = Byte} {tag₂ = Bit} 
                                𝔹[ m ] 𝔹[ 8 * m ]
      -- refl
      𝕓≡𝕓 : Taut 𝕓 𝕓
      -- sym
      𝕓sym : Taut 𝕓₁ 𝕓₂ → Taut 𝕓₂ 𝕓₁
      -- trans
      𝕓trans : Taut 𝕓₁ 𝕓₂ → Taut 𝕓₂ 𝕓₃ → Taut 𝕓₁ 𝕓₃

  private
    variable
      𝓁 : Level

  record RepOf {𝓁} {Ty : Set 𝓁} (A : Ty) : Set where
    field
      size : (tag : BitOrByte) → ℕ
      bitRep : BitRep tag (size tag)

  forgetType : ∀ {𝓁} {Ty : Set 𝓁} {A : Ty} →
               RepOf A → Σ[ m ∈ ℕ ] BitRep tag m
  forgetType {tag = tag} record {
    size = size ;
    bitRep = bitRep } = (size tag , bitRep)

  module Padding where

    -- Pad a given BitRep to a larger size
    padToSize : ∀ m {n} → n ≤ m → BitRep tag n → BitRep tag m
    padToSize m {n} n≤m 𝕓 = 
      subst (BitRep _) (m∸n+n≡m n≤m)
        (𝔹[ m ∸ n ] ++ 𝕓)

    -- Takes a vector of dependent pairs of numbers and 
    -- returns the lub, along with a vector of proofs that 
    -- each number is less-than-or-equal to the lub
    ⨆-vec-pfs : ∀ {𝓁} {B : ℕ → Set 𝓁} →
                Vec (Σ ℕ B) n →
                Σ[ ⨆-m ∈ ℕ ]
                Vec (Σ[ mᵢ ∈ ℕ ] B mᵢ × mᵢ ≤ ⨆-m) n
    ⨆-vec-pfs [] = 0 , []
    ⨆-vec-pfs {B = B} ((m , b) ∷ xs) with ⨆-vec-pfs xs
    ... | (⨆-m , pfs) =
      let
        f : Σ[ mᵢ ∈ ℕ ] (B mᵢ × mᵢ ≤ ⨆-m) →
            Σ[ mᵢ ∈ ℕ ] (B mᵢ × mᵢ ≤ m ⊔ ⨆-m)
        f (mᵢ , (b , mᵢ≤⨆-m)) = mᵢ , (b ,′ m≤n⇒m≤o⊔n m mᵢ≤⨆-m)
      in
      m ⊔ ⨆-m , (m , (b ,′ m≤m⊔n _ _)) ∷ (map f pfs)

    ⨆-vec : ∀ {𝓁} {B : ℕ → Set 𝓁} →
                Vec (Σ ℕ B) n → ℕ
    ⨆-vec xs = proj₁ (⨆-vec-pfs xs)

    -- Pads a vector of BitReps to the largest size BitRep
    -- in the vector
    padBitReps : (𝕓s : Vec (Σ[ mᵢ ∈ ℕ ] BitRep tag mᵢ) n) →
                 Vec (BitRep tag (⨆-vec 𝕓s)) n
    padBitReps {tag = tag} 𝕓s with ⨆-vec-pfs 𝕓s
    ... | ⨆-m , 𝕓s-pfs =
      let
        f : Σ[ mᵢ ∈ ℕ ] BitRep tag mᵢ × mᵢ ≤ ⨆-m → 
            BitRep tag ⨆-m
        f (mᵢ , (𝕓 , mᵢ≤⨆-m)) = padToSize ⨆-m mᵢ≤⨆-m 𝕓
      in
      map f 𝕓s-pfs

