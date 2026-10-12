{-# OPTIONS --safe --prop #-}

open import Data.Product

open import heap

module correct-compiler where

module compiler (Exp : Set) {- Expression Language -}
                (Value : Set) {- Value Types -}
                {- Big-step semantics -}
                (_,_,_⇓_,_ : Exp → Heap Value → Location → 
                             Heap Value → Location → Prop) 
                where
  Rep : Set₁
  Rep = {- entry point : -} Location × Heap Value → Prop
  
  Representable : Set → Set₁
  Representable A = A → Rep

  Implements : ∀ {A B : Set} →
               (Rᴬ : Representable A) →
               (Rᴮ : Representable B) →
               (f : A → B) →
               (e : Exp) → Prop
  Implements {A} {B} Rᴬ Rᴮ f e =
    -- Forall valid input representations ...
    ∀ (a : A) (lᵃ : Location) (hᵃ : Heap Value) →
    Rᴬ a (lᵃ , hᵃ) →
    -- ... evaluating that representation in the expression langauge ...
    ∀ (lᵇ : Location) (hᵇ : Heap Value) →
    (e , hᵃ , lᵃ ⇓ hᵇ , lᵇ) →
    -- ... gives back a valid representation of the function application.
    Rᴮ (f a) (lᵇ , hᵇ)

