{-# OPTIONS --safe #-}

open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Vec

module correct-compiler where

-- How "virtual" do we want to be? Should this be Nat instead?
Word = Vec Bool 32
Location = Word

zeroW : Word
zeroW = replicate 32 false

-- TODO: could use tries to represent heaps
-- A heap is a partial map from locations to values
Heap = Location → Maybe Word

{- -- Countable number of registers for register allocation
Reg = ℕ
RegState = Reg → Word

initRegState : RegState
initRegState _ = zeroW -}

initHeap : Heap
initHeap _ = nothing

Rep = Location × Heap → Set
Representable : Set → Set₁
Representable A = A → Rep

module compiler (Exp : Set) {- Expression Language -}
                {- Big-step semantics -}
                (_,_⇓_ : Exp → Location × Heap → Location × Heap → Set)
                where

  Implements : ∀ {A B : Set} →
               (Rᴬ : Representable A) →
               (Rᴮ : Representable B) →
               (f : A → B) →
               (e : Exp) → Set
  Implements {A} {B} Rᴬ Rᴮ f e =
    -- Forall valid input representations ...
    ∀ (a : A) (lᵃ : Location) (hᵃ : Heap ) →
    Rᴬ a (lᵃ , hᵃ) →
    -- ... evaluating that representation in the expression langauge ...
    ∀ (lᵇ : Location) (hᵇ : Heap ) →
    (e , (lᵃ , hᵃ) ⇓ (lᵇ , hᵇ)) →
    -- ... gives back a valid representation of the function application.
    Rᴮ (f a) (lᵇ , hᵇ)

