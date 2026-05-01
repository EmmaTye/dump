{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Sigma
open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; inspect; [_])

module FinTT where

  private
    variable
      A B C : Set

  -- A finite type is isomorphic to some Fin size
  record FinTy (Ty : Set) : Set where
    field
      size : ℕ
      toTy : Fin size → Ty
      toFin : Ty → Fin size
      fin→ty : ∀ (i : Fin size) → toFin (toTy i) ≡ i
      ty→fin : ∀ (t : Ty) → toTy (toFin t) ≡ t

  open FinTy ⦃ ... ⦄

  _exp_ : ℕ → ℕ → ℕ
  n exp 0 = 1
  n exp (suc m) = n * (n exp m)

  _⇒_ : (A B : Set) → ⦃ FinTy A ⦄ → ⦃ FinTy B ⦄
      → Set
  _⇒_ A B ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = 
    Vec (Fin (size ⦃ Bᶠ ⦄)) (size ⦃ Aᶠ ⦄)

  instance
    ⇒ᶠ : ∀ ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄ → FinTy (A ⇒ B)
    ⇒ᶠ {A} {B} ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = record { 
        size = size⇒;
        toTy = toTy⇒;
        toFin = toFin⇒;
        fin→ty = fin→ty⇒;
        ty→fin = ty→fin⇒
      }
      where
        size⇒ = (size ⦃ Bᶠ ⦄) exp (size ⦃ Aᶠ ⦄)

        toTy⇒ : Fin size⇒ → A ⇒ B
        toTy⇒ f = ?

        toFin⇒ : (A ⇒ B) → Fin size⇒
        toFin⇒ bs = ?

        fin→ty⇒ : (i : Fin size⇒) → toFin⇒ (toTy⇒ i) ≡ i
        fin→ty⇒ i = ?

        ty→fin⇒ : (bs : A ⇒ B) → toTy⇒ (toFin⇒ bs) ≡ bs
        ty→fin⇒ bs = ?
        -- let (size B) = n
        -- [b0 b0 ... b0] [b0 b1 ... b0] ... [b0 bn ... b0]
        -- [b1 b0 ... b0] [b1 b1 ... b0] ... [b1 bn ... b0]
        -- ...            ...                ...
        -- [bn b0 ... b0] [bn b1 ... b0] ... [bn bn ... b0]
        -- in (size A) dimensions
        -- uhh, list out every entry? might need to change
        -- definition of size and Fin to carry more information 
        -- about how far through the Bᴬ we are...
        -- maybe size should be a type of Numeric instance, 
        -- where Numeric has a function toNat : A → ℕ?
        -- then we can make the size for ⇒ be an indexed-
        -- inductive type that carries an index for A and B
        -- still need to find a way to structure Fin better...

  _$_ : ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄ → A ⇒ B → A → B
  f $ a =
    let
      fᵃ = toFin a
      fᵇ = lookup f fᵃ
    in
    toTy fᵇ

  _∘_ : ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄ ⦃ Cᶠ : FinTy C ⦄ →
        B ⇒ C → A ⇒ B → A ⇒ C
  _∘_ g = map (lookup g)

  -- Composition of finite maps is the same as applying in succession
  [g∘f]$a≡g$f$a : ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄
                  ⦃ Cᶠ : FinTy C ⦄
                  {f : _⇒_ A B ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄}
                  {g : _⇒_ B C ⦃ Bᶠ ⦄ ⦃ Cᶠ ⦄}
                  {a : A} →
                  ((_∘_ ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ ⦃ Cᶠ ⦄ g f) $ a)
                  ≡ _$_ ⦃ Bᶠ ⦄ ⦃ Cᶠ ⦄ g (f $ a)
  [g∘f]$a≡g$f$a ⦃ Bᶠ = Bᶠ ⦄ {f = f} {g = g} {a = a} =
    let
      b = lookup f (toFin a)
      lookup-map-fin = lookup-map (toFin a) (lookup g) f
    in
    cong toTy
      (trans lookup-map-fin
             (cong (lookup g) (sym (fin→ty ⦃ Bᶠ ⦄ b))))

