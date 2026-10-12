open import Data.Bool
open import Data.Fin
  hiding (fold)
open import Data.Fin.Properties
open import Data.Maybe
  hiding (map)
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
  hiding (map; curry)
open import Data.Unit
open import Data.Vec
open import Data.Vec.Properties
open import Function.Base
  using (_∘_)
open import Relation.Binary.PropositionalEquality

open import FinTT
open import FinModel
open import FunTT

module FinFunModel where

  private
    variable
      A B C : Set
      m n p : ℕ
      i j : Fin _
      Aᵗ Bᵗ Cᵗ Dᵗ : FinTypes.Ty

  module FunTy where

    open FinTy ⦃ ... ⦄
    open FinTypes using (Ty)

    funToFin-cong : ∀ {f g : Fin m → Fin n} → f ≗ g →
                    funToFin f ≡ funToFin g
    funToFin-cong {zero} eqLam = refl
    funToFin-cong {suc m} {_} {f} {g} eqLam =
      cong₂ combine (eqLam zero) (funToFin-cong (eqLam ∘ suc))

    instance
      ⇛ᶠ : ∀ {m n} ⦃ Aᶠ : FinTy A m ⦄ ⦃ Bᶠ : FinTy B n ⦄
           → FinTy (Vec (Fin n) m) (n ℕ.^ m)
      ⇛ᶠ {A} {B} {m} {n} ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ = record {
          toTy = toTy⇛;
          toFin = toFin⇛;
          fin→ty = fin→ty⇛;
          ty→fin = ty→fin⇛
        }
        where
          toTy⇛ : _
          toTy⇛ = tabulate ∘ finToFun

          toFin⇛ : _
          toFin⇛ = funToFin ∘ lookup

          fin→ty⇛ : (i : Fin (n ℕ.^ m)) →
                    toFin⇛ (toTy⇛ i) ≡ i
          fin→ty⇛ i =
            trans (funToFin-cong (lookup∘tabulate (finToFun {n} {m} i)))
                  (funToFin-finToFin {m} {n} i)

          ty→fin⇛ : (bs : Vec (Fin n) m) →
                    toTy⇛ (toFin⇛ bs) ≡ bs
          ty→fin⇛ bs = trans (tabulate-cong (finToFun-funToFin (lookup bs)))
                             (tabulate∘lookup bs)

    _⇛_ : Ty → Ty → Ty
    (A , (m , Aᶠ)) ⇛ (B , (n , Bᶠ)) =
      (Vec (Fin n) m , (n ℕ.^ m , ⇛ᶠ ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄))

    _$_ : ∀ ⦃ Aᶠ : FinTy A m ⦄ ⦃ Bᶠ : FinTy B n ⦄ →
          Vec (Fin n) m → A → B
    f $ a =
      let
        fᵃ = toFin a
        fᵇ = lookup f fᵃ
      in
      toTy fᵇ

    _∘′_ : ∀ ⦃ Aᶠ : FinTy A m ⦄ ⦃ Bᶠ : FinTy B n ⦄
            ⦃ Cᶠ : FinTy C p ⦄ →
          Vec (Fin p) n → Vec (Fin n) m → Vec (Fin p) m
    _∘′_ g = map (lookup g)

    -- Composition of finite maps is the same as applying in succession
    [g∘′f]$a≡g$f$a : ∀ ⦃ Aᶠ : FinTy A m ⦄
                       ⦃ Bᶠ : FinTy B n ⦄
                       ⦃ Cᶠ : FinTy C p ⦄
                       (f : Vec (Fin n) m)
                       (g : Vec (Fin p) n)
                       (a : A) →
                     ((_∘′_ ⦃ Aᶠ ⦄ ⦃ Bᶠ ⦄ ⦃ Cᶠ ⦄ g f) $ a)
                     ≡ _$_ ⦃ Bᶠ ⦄ ⦃ Cᶠ ⦄ g (f $ a)
    [g∘′f]$a≡g$f$a ⦃ Bᶠ = Bᶠ ⦄ f g a =
      let
        b = lookup f (toFin a)
        lookup-map-fin = lookup-map (toFin a) (lookup g) f
      in
      cong toTy
        (trans lookup-map-fin
               (cong (lookup g) (sym (fin→ty ⦃ Bᶠ ⦄ b))))

  module FunModel where
    open FinModel.FinModel
    open FinTypes
    open PartialIsos
    open FunTy
    open FinTy ⦃ ... ⦄

    𝟘⇛a : ∀ {Aᵗ : Ty} → (𝟘 ⇛ Aᵗ) ≅ 𝟙
    𝟘⇛a {Aᵗ} = record {
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        _⇐ : Tm 𝟙 → Tm (𝟘 ⇛ Aᵗ)
        tt ⇐ = []

        idl : {a : Tm (𝟘 ⇛ Aᵗ)} → tt ⇐ ≡ a
        idl {[]} = refl

        idr : {b : Tm 𝟙} → tt ≡ b
        idr {tt} = refl

    allᵢ : (f : A → Fin n → Bool) → Vec A n → Bool
    allᵢ {n = zero} f [] = true
    allᵢ {n = suc n} f (x ∷ xs) = 
      f x zero ∧ allᵢ (λ x → f x ∘ suc) xs 

     -- ⊑ and ⇛ laws
     -- Given A ⊑ A', transform a function from A → B into 
     -- A' → B by:
     -- - if (a'→ma a') ≡ just a, then return (a→b a)
     -- - otherwise, pick a point in B (namely 0) and send a' there
     -- Go backwards by testing if all A' / A map to the same point (namely 0) 
     -- - if so, then restrict the domain to A
     -- - otherwise, return nothing
     -- Requires - B to be pointed, A' to be traversable
    ⇛⊑domain : ∀ {Aᵗ Aᵗ' Bᵗ : Ty} →
               Aᵗ ⊑ Aᵗ' →
               𝟙 ⊑ Bᵗ →
               (Aᵗ ⇛ Bᵗ) ⊑ (Aᵗ' ⇛ Bᵗ)
    ⇛⊑domain {A , sizeᵃ , finIsoᵃ}
             {A' , sizeᵃ' , finIsoᵃ'}
             {B , sizeᵇ , finIsoᵇ}
             record { ⇒ = a→a';
                      _⇐ = a'→ma;
                      idl = ida→a';
                      idr = ida'→ma }
             record { ⇒ = 𝟙→b;
                      _⇐ = b→𝟙;
                      idl = _;
                      idr = _ } =
      record {
          ⇒ = a⇛b→a'⇛b;
          _⇐ = a'⇛b→m[a⇛b];
          idl = {! !};
          idr = {! !}
      } where
        b* = 𝟙→b tt
        iᵇ* = toFin ⦃ finIsoᵇ ⦄ b*

        a⇛b→a'⇛b : Vec (Fin sizeᵇ) sizeᵃ → Vec (Fin sizeᵇ) sizeᵃ'
        a⇛b→a'⇛b bᵃ = tabulate 
          (maybe (lookup bᵃ ∘ toFin ⦃ finIsoᵃ ⦄) iᵇ* 
           ∘ a'→ma ∘ toTy ⦃ finIsoᵃ' ⦄)

        a'⇛b→m[a⇛b] : Vec (Fin sizeᵇ) sizeᵃ' →
                      Maybe (Vec (Fin sizeᵇ) sizeᵃ)
        a'⇛b→m[a⇛b] bᵃ' = 
          if allᵢ ? bᵃ'
          then just (tabulate 
                     (lookup bᵃ' ∘ toFin ⦃ finIsoᵃ' ⦄ ∘ a→a' 
                      ∘ toTy ⦃ finIsoᵃ ⦄))
          else nothing
          where
            targetsGarbage : Fin sizeᵇ → Fin sizeᵃ' → Bool
            targetsGarbage iᵇ iᵃ' with a'→ma (toTy ⦃ finIsoᵃ' ⦄ iᵃ')
            ... | just x = true
            ... | nothing = ? iᵇ iᵇ*

    postulate
      a⇛𝟘 : ∀ {Aᵗ : Ty} → Tm Aᵗ → (Aᵗ ⇛ 𝟘) ≅ 𝟘

      𝟙⇛a : ∀ {Aᵗ : Ty} → (𝟙 ⇛ Aᵗ) ≅ Aᵗ
      a⇛𝟙 : ∀ {Aᵗ : Ty} → (Aᵗ ⇛ 𝟙) ≅ 𝟙

      ＋⋆⇛ : ∀ {Aᵗ Bᵗ Cᵗ : Ty} → 
             ((Aᵗ ＋ Bᵗ) ⇛ Cᵗ) ≅ ((Aᵗ ⇛ Cᵗ) ⋆ (Bᵗ ⇛ Cᵗ))
      ⋆⇛ : ∀ {Aᵗ Bᵗ Cᵗ : Ty} →
           (Aᵗ ⇛ (Bᵗ ⋆ Cᵗ)) ≅ ((Aᵗ ⇛ Bᵗ) ⋆ (Aᵗ ⇛ Cᵗ))
      curry : ∀ {Aᵗ Bᵗ Cᵗ : Ty} →
              ((Aᵗ ⋆ Bᵗ) ⇛ Cᵗ) ≅ (Aᵗ ⇛ (Bᵗ ⇛ Cᵗ))

      -- ≅ and ⇛ laws
      ⇛≅domain : ∀ {Aᵗ Aᵗ' Bᵗ : Ty} →
                 Aᵗ ≅ Aᵗ' →
                 (Aᵗ ⇛ Bᵗ) ≅ (Aᵗ' ⇛ Bᵗ)
      ⇛≅codomain : ∀ {Aᵗ Bᵗ Bᵗ' : Ty} →
                   Bᵗ ≅ Bᵗ' →
                   (Aᵗ ⇛ Bᵗ) ≅ (Aᵗ ⇛ Bᵗ')

      ⇛⊑codomain : ∀ {Aᵗ Bᵗ Bᵗ' : Ty} →
                    Bᵗ ⊑ Bᵗ' →
                    (Aᵗ ⇛ Bᵗ) ⊑ (Aᵗ ⇛ Bᵗ')

  -- TODO: not sure why agda is complaining about the difference between PartialIsos.⊑ and .BaseTT.BaseTT.PI BaseTT.PartialIso.⊑...
--  instance
--    FunTT⇛ : FunTT
--    FunTT⇛ = record {FunModel}

