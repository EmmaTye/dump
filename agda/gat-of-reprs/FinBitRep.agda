open Agda.Primitive

open import Data.Fin
open import Data.Nat as ℕ
  using (ℕ)
open import Data.Nat.Properties
open import Data.Nat.Logarithm
open import Data.Product
  hiding (map)
open import Data.Vec
  hiding (_++_)
open import Function.Base
  using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; cong)

open import BaseTT
open import BitRep
open import FinTT

module FinBitRep where

  private
    variable
      n m : ℕ

  ⌈_/_⌉ : (m n : ℕ) .{{_ : ℕ.NonZero n}} → ℕ
  ⌈ m / n ⌉ with m ℕ.% n
  ... | ℕ.zero = m ℕ./ n
  ... | ℕ.suc _ = ℕ.suc (m ℕ./ n)

  -- Not defined as an instance since we want instance
  -- resolution for RepOf to prioritise using the algebraic
  -- structure
  -- finBitRep is for use with terminals such as int8, etc.
  finBitRep : {A : Set} → ⦃ Aᶠ : FinTy A n ⦄ →
              RepOf A
  finBitRep {n = n} = record {
      size = size;
      bitRep = bitRep
    } where
      size : BitOrByte → ℕ
      size Bit = ⌈log₂ n ⌉
      size Byte = ⌈ (size Bit) / 8 ⌉

      bitRep : {tag : BitOrByte} → BitRep tag (size tag)
      bitRep {tag} = 𝔹[ size tag ]

  private
    variable
      𝓁 : Level

  module BaseReps {𝓁} (BaseTys : BaseTypes {𝓁}) where
  
    open BaseTypes BaseTys
    open RepOf ⦃ ... ⦄

    private
      variable
        A B C D : Ty
        tag : BitOrByte

    instance
      𝟙bitRep : RepOf 𝟙
      size ⦃ 𝟙bitRep ⦄ tag = 0
      bitRep ⦃ 𝟙bitRep ⦄ = ϵ

    instance
      ＋bitRep : ⦃ RepOf A ⦄ → ⦃ RepOf B ⦄ →
                 RepOf (A ＋ B)
      size ⦃ ＋bitRep ⦃ arep ⦄ ⦃ brep ⦄ ⦄ tag =
        (toByte tag 1) ℕ.+
        ((size ⦃ arep ⦄ tag) ℕ.⊔ (size ⦃ brep ⦄ tag))
      bitRep ⦃ ＋bitRep ⦃ arep ⦄ ⦃ brep ⦄ ⦄ {tag} =
        let
          paddedReps = Padding.padBitReps {tag = tag}
            ((size ⦃ arep ⦄ tag , bitRep ⦃ arep ⦄) ∷
             (size ⦃ brep ⦄ tag , bitRep ⦃ brep ⦄) ∷ [] )
        in
        U[ 2 , ℕ.s≤s (ℕ.s≤s ℕ.z≤n) ,
           -- Need to prove that ⨆-vec a ∷ b ∷ [] ≡ a ⊔ b
           subst (λ x → Vec (BitRep tag x) 2)
                 (cong (ℕ._⊔_ (size ⦃ arep ⦄ tag)) 
                   (⊔-identityʳ _))
                 paddedReps ]

    instance
      ⋆bitRep : ⦃ RepOf A ⦄ → ⦃ RepOf B ⦄ →
                RepOf (A ⋆ B)
      size ⦃ ⋆bitRep ⦃ arep ⦄ ⦃ brep ⦄ ⦄ tag =
        size ⦃ arep ⦄ tag ℕ.+ size ⦃ brep ⦄ tag
      bitRep ⦃ ⋆bitRep ⦃ arep ⦄ ⦃ brep ⦄ ⦄ =
        bitRep ⦃ arep ⦄ ++ bitRep ⦃ brep ⦄

    RepsOf : (As : Vec Ty n) → Set
    RepsOf {n = n} As = (i : Fin n) → RepOf (lookup As i)

    -- Maximum size sums of 256
    -- For larger sums, separate out into multiple (balanced)
    -- sums
    SumBitRep : {As : Vec Ty n} → n ℕ.≤ byte → 
                RepsOf As → RepOf (Sum As)
    SumBitRep {n = n} n≤byte reps =
      let
        𝕓s tag = tabulate (forgetType {tag = tag} ∘ reps)
        size tag = toByte tag 1 ℕ.+ Padding.⨆-vec (𝕓s tag)
        bitRep {tag} = U[ n , n≤byte , 
                          Padding.padBitReps (𝕓s tag) ]
      in
      record {
        size = size;
        bitRep = bitRep
      }
    
    ProdBitRep : {As : Vec Ty n} → RepsOf As → 
                 RepOf (Prod As)
    ProdBitRep {n = n} reps =
      record {
        size = sizeProd;
        bitRep = λ {tag} → bitRepOf (𝕓s tag)
      } where
        𝕓s : (tag : BitOrByte) → Vec _ n
        𝕓s tag = tabulate (forgetType {tag = tag} ∘ reps)

        sum′ : ∀ {n} {B : ℕ → Set} → Vec (Σ ℕ B) n → ℕ
        sum′ = foldr′ (λ 𝕓ₐ m → proj₁ 𝕓ₐ ℕ.+ m) 0

        sizeProd : _
        sizeProd tag = sum′ (𝕓s tag)
 
        bitRepOf : ∀ {n} 
                   (xs : Vec (Σ[ m ∈ ℕ ] BitRep tag m) n) → 
                   BitRep tag (sum′ xs)
        bitRepOf [] = ϵ
        bitRepOf ((m , 𝕓) ∷ xs) = 𝕓 ++ (bitRepOf xs)

