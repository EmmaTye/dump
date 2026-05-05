open import Data.Fin
  hiding (fold)
open import Data.Fin.Properties
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality

open import FinTT
open import FunTT

module FinFunModel where

  private
    variable
      A B C : Set
      m n : ℕ
      i j : Fin _

  open FinTy ⦃ ... ⦄
  
  _⇛_ : (A B : Set) → ⦃ FinTy A ⦄ → ⦃ FinTy B ⦄
        → Set
  _⇛_ A B ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = 
    Vec (Fin (size ⦃ Bᶠ ⦄)) (size ⦃ Aᶠ ⦄)

  _$_ : ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄ → A ⇛ B → A → B
  f $ a =
    let
      fᵃ = toFin a
      fᵇ = lookup f fᵃ
    in
    toTy fᵇ

  _∘_ : ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄ ⦃ Cᶠ : FinTy C ⦄ →
        B ⇛ C → A ⇛ B → A ⇛ C
  _∘_ g = map (lookup g)

  -- Ordering relation helpers
  n≤n : ∀ {n} → n ℕ.≤ n
  n≤n {zero} = ℕ.z≤n
  n≤n {suc n} = ℕ.s≤s n≤n

  sm≤n⁻¹ : ∀ {m n} → suc m ℕ.≤ n → m ℕ.≤ n
  sm≤n⁻¹ {zero} (s≤s m≤n) = ℕ.z≤n
  sm≤n⁻¹ {suc m} (s≤s m≤n) = s≤s (sm≤n⁻¹ m≤n)

  -- iterateᶠ {n} f = f n ∷ f n-1 ∷ ... ∷ f (zero) ∷ []
  -- Specific version of iterate from Data.Fin for Vec
  iterateᶠ : ∀ {n} → (Fin (suc n) → A)
             → Vec A (suc n)
  iterateᶠ {A} {n} f = iterateᶠ' (suc n) n≤n
    where
      iterateᶠ' : (m : ℕ) → .(m ℕ.≤ suc n) → Vec A m
      iterateᶠ' zero _ = []
      iterateᶠ' (suc m) sm≤sn = (f (inject≤ (fromℕ m) sm≤sn))
                             ∷ (iterateᶠ' m (sm≤n⁻¹ sm≤sn))

  -- TODO: prove
  -- (I think this is necessary to prove ⇛ is an instance of FinTy)
  postulate
    lookup-iterateᶠ : ∀ {n} {f : Fin (suc n) → A}
                       → (i : Fin (suc n)) → 
                       lookup (iterateᶠ f) i ≡ f i

  instance
    ⇛ᶠ : ∀ ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄ → FinTy (A ⇛ B)
    ⇛ᶠ {A} {B} ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = record {
        size = size⇛;
        toTy = toTy⇛;
        toFin = toFin⇛;
        fin→ty = fin→ty⇛;
        ty→fin = ty→fin⇛
      }
      where
        size⇛ = size ⦃ Bᶠ ⦄ ℕ.^ size ⦃ Aᶠ ⦄

        toTy⇛ : Fin size⇛ → A ⇛ B
        toTy⇛ i with size ⦃ Aᶠ ⦄
        ... | zero = []
        ... | suc n =
          iterateᶠ (finToFun {size ⦃ Bᶠ ⦄} {suc n} i)

        toFin⇛ : (A ⇛ B) → Fin size⇛
        toFin⇛ bs = funToFin {size ⦃ Aᶠ ⦄} {size ⦃ Bᶠ ⦄} 
          (lookup bs)

        -- TODO: prove
        postulate fin→ty⇛ : (i : Fin size⇛) → toFin⇛ (toTy⇛ i) ≡ i

        postulate ty→fin⇛ : (bs : A ⇛ B) → toTy⇛ (toFin⇛ bs) ≡ bs

  -- Composition of finite maps is the same as applying in succession
  [g∘f]$a≡g$f$a : ⦃ Aᶠ : FinTy A ⦄ ⦃ Bᶠ : FinTy B ⦄
                  ⦃ Cᶠ : FinTy C ⦄
                  {f : _⇛_ A B ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄}
                  {g : _⇛_ B C ⦃ Bᶠ ⦄ ⦃ Cᶠ ⦄}
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

