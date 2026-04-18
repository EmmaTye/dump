open Agda.Primitive

open import Agda.Builtin.Sigma
  renaming (Σ to _×ᴰ_; _,_ to _,ᴰ_)
open import Agda.Builtin.Unit

open import Data.Empty
open import Data.Fin
  renaming (_+_ to _+F_)
open import Data.Fin.Patterns
open import Data.Integer
  renaming (_+_ to _+ℤ_)
open import Data.List
open import Data.Nat
open import Data.Product
  using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; inspect; [_])

module cal where

  variable
    n m : ℕ
    X : Set
    Σ : ℕ → Set
    A B : Set

  Alg : (Σ : ℕ → Set) → (A : Set) → Set
  Alg Σ A = {n : ℕ} → Σ n → (Fin n → A) → A

  variable
    α α₁ α₂ : Alg _ _

  data 𝐄 : Set where
    𝐞 : 𝐄

  data 𝐈 : Set where
    𝐢 : 𝐈

  data 𝐌 : Set where
    𝐦 : 𝐌

  gΣ : ℕ → Set
  gΣ 0 = 𝐄 -- e, only 0-ary op (identity)
  gΣ 1 = 𝐈 -- i, only unary op (inverse)
  gΣ 2 = 𝐌 -- m, only binary op (group op)
  gΣ (suc (suc (suc _))) = ⊥ -- no other operations of greater arity

  ℤ-α : Alg gΣ ℤ
  ℤ-α {0} _ a⁰ = 0ℤ -- 0 is the unit
  ℤ-α {1} _ a¹ = - (a¹ 0F) -- -_ is the inverse
  ℤ-α {2} _ a² = (a² 0F) +ℤ (a² 1F) -- addition if the group op
  ℤ-α {suc (suc (suc _))} ()

  -- Forgetful functor
  U : Alg Σ A → Set
  U {A = A} _ = A

  -- Associated signature endofunctor
  P : {Σ : ℕ → Set} → Set → Set
  P {Σ} x = ℕ ×ᴰ (λ n → Σ n × (Fin n → x))
  
  data Term (Σ : ℕ → Set) (X : Set) : Set where
    ηₓ : (x : X) → Term Σ X
    ⟨_⨟_⟩ : (o : Σ m) → (Fin m → Term Σ X) → Term Σ X

  variable
    t t₁ t₂ : Term _ _

  -- Free algebra on Set (left adjoint of U)
  F : {Σ : ℕ → Set} → (X : Set) → Alg Σ (Term Σ X)
  F {Σ} X = λ o ts → ⟨ o ⨟ ts ⟩

  -- Evaluate an algebra in a Term, given a variable assignment
  evalα : {X : Set} → (varA : X → A) → Alg Σ A → Term Σ X → A
  evalα varA α (ηₓ x) = varA x
  evalα {A = A} varA α ⟨ o ⨟ ts ⟩ =
    let
      as : Fin _ → A
      as = λ fm → evalα varA α (ts fm)
    in
    α o as

  -- Equation in n variables
  Eq : (Σ : ℕ → Set) (n : ℕ) → Set
  Eq Σ n = (Term Σ (Fin n)) × (Term Σ (Fin n))

  -- An algebra α satisfies an equation (Term × Term) in n vars
  -- iff for all n-tuples Aⁿ, evaluating α on both sides of the
  -- equation results in the same term
  Satisfies : {Σ : ℕ → Set} → Alg Σ A → Eq Σ n → Set
  Satisfies {A = A} {n = n} α (t₁ , t₂) =
    (as : Fin n → A) →
    evalα as α t₁ ≡ evalα as α t₂

  -- An equational theory for a signature is
  -- a finite set of equations for every n ∈ ℕ
  EqTh : (Σ : ℕ → Set) → Set
  EqTh Σ = (n : ℕ) → ℕ ×ᴰ
             -- Finite set of size m
             (λ m → Fin m →
                    Eq Σ n)

  -- A presentation of an equational theory is an algebra
  -- that satisfies all the equations in the EqTh
  EqAlg : (Σ : ℕ → Set) → EqTh Σ → (A : Set) → Set
  EqAlg Σ Eₙ A = (Alg Σ A) ×ᴰ (λ α →
    -- For every n ∈ ℕ
    (n : ℕ) →
      let
        (m ,ᴰ Es) = Eₙ n
      in
      -- Satisfy every equation in n vars
      (fm : Fin m) → Satisfies α (Es fm))

  -- Smart constructors for group terms
  mᵍ : Term gΣ X × Term gΣ X → Term gΣ X 
  mᵍ (t₁ , t₂) = ⟨ 𝐦 ⨟ ts ⟩
    where
      ts : Fin 2 → Term gΣ _
      ts 0F = t₁
      ts 1F = t₂

  eᵍ : Term gΣ X
  eᵍ = ⟨ 𝐞 ⨟ (λ ()) ⟩

  iᵍ : Term gΣ X → Term gΣ X
  iᵍ t = ⟨ 𝐢 ⨟ (λ 0F → t) ⟩

  -- The equational theory for groups
  grpTh : EqTh gΣ
  grpTh 0 = (0 ,ᴰ (λ ()))
  -- 4 equations in 1 variable
  grpTh 1 = (4 ,ᴰ eqs)
    where
      x = 0F
  
      eqs : Fin 4 → Eq gΣ 1
      eqs 0F = (mᵍ (eᵍ , ηₓ x) , ηₓ x) -- left id
      eqs 1F = (mᵍ (ηₓ x , eᵍ) , ηₓ x) -- right id
      eqs 2F = (mᵍ (iᵍ (ηₓ x) , ηₓ x) , eᵍ) -- left inverse
      eqs 3F = (mᵍ (ηₓ x , iᵍ (ηₓ x)) , eᵍ) -- right inverse
  grpTh 2 = (0 ,ᴰ (λ ()))
  -- 1 equation in 3 variables
  grpTh 3 = (1 ,ᴰ (λ 0F → ass))
    where
      x = 0F
      y = 1F
      z = 2F

      ass : Eq gΣ 3
      ass = ( mᵍ (mᵍ ( ηₓ x , ηₓ y ) , ηₓ z) , 
              mᵍ ( ηₓ x , mᵍ ( ηₓ y , ηₓ z ) ) )
  grpTh (suc (suc (suc (suc n)))) = (0 ,ᴰ (λ ()))

  -- TODO: prove that ℤ is a representations of an equational
  -- theory for groups using Data.Integer.Properties

