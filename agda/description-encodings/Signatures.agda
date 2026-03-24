{-# OPTIONS --erasure #-}

open Agda.Primitive

module Signatures where

variable
  𝓁 : Level

data Tel {𝓁 : Level} : Set (lsuc 𝓁)  where
  · : Tel
  _*_ : (A : Set 𝓁) → (A → Tel {𝓁}) → Tel

data Spine {𝓁 : Level} : Tel -> Set (lsuc 𝓁) where
  · : Spine ·
  _,_ : ∀ {@0 A : Set 𝓁} {@0 Δ : A → Tel} →
        (a : A) → Spine (Δ a) → Spine (A * Δ)

_**_ : ∀ {𝓁} (Δ : Tel) → (X : Spine Δ → Set 𝓁) → Tel {𝓁}
· ** X = X · * (λ x → ·)
_**_ {𝓁 = 𝓁} (A * Δ) X = 
  A * (λ A → 
    let
      X' : Spine (Δ A) → Set 𝓁
      X' δ = X (A , δ)
    in
    (Δ A) ** X')

_,,_ : {@0 Δ : Tel} {X : Spine Δ → Set 𝓁} →
       (δ : Spine Δ) → X δ → Spine (Δ ** X)
· ,, x = x , ·
(a , δ) ,, x = a , (δ ,, x)

data OpTerm {𝓁} (T : Tel {𝓁}) : Set (lsuc 𝓁) where
  ιᵀ : Spine T → OpTerm T

data Op {𝓁} (I : Tel {𝓁}) (O : Tel {𝓁}) : Set (lsuc 𝓁) where
  ι' : OpTerm O → Op I O
  _→ⁱ_ : OpTerm I → Op I O → Op I O
  _→ᵉ_ : (A : Set 𝓁) → (A → Op I O) → Op I O

ι : ∀ {𝓁} {I : Tel {𝓁}} {O : Tel} → Spine O → Op I O
ι δ = ι' (ιᵀ δ)

liftᵉ : ∀ {𝓁} {I : Tel {𝓁}} {O : Tel} {A : Set 𝓁} → (A → Op I O) → Op I O
liftᵉ {A = A} lam = A →ᵉ lam

data Sig {𝓁} (I : Tel {𝓁}) (O : Tel) : Set (lsuc 𝓁) where
  ϵ : Sig I O
  _◃_ : Op I O → Sig I O → Sig I O

variable
  Δ I O : Tel
  δ δ' : Spine _
  X Y : Spine _ → Set _
  Σ : Sig I O

