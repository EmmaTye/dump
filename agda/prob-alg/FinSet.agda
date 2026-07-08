open import Level as L using ()
open import Function.Base
open import Data.Nat as ℕ
  using (ℕ)
open import Data.Fin
open import Data.Product
  hiding (map)
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
  using (Rel)

open import Categories.Category.Core

module FinSet where

private
  variable
    m n : ℕ
    i j : Fin _

record FinSetObj : Set₁ where
  field
    Ty : Set
    size : ℕ

  field
    toFin : Ty → Fin size
    fromFin : Fin size → Ty
    inverseˡ : ∀ {a : Ty} → fromFin (toFin a) ≡ a
    inverseʳ : ∀ {i : Fin size} → toFin (fromFin i) ≡ i

record Non⊥ (A : FinSetObj) : Set where
  open FinSetObj
  field
    nonZero : ℕ.NonZero (A .size)

lower' : ∀ (i : Fin (ℕ.suc n)) → .(i > zero {n}) → Fin n
lower' (suc i) _ = i

-- Irrelevant second projection
record Subset {ℓ o} (A : Set ℓ) (P : A → Set o) : Set (ℓ L.⊔ o) where
  constructor _#_
  field
    elem : A
    .certificate : P elem

subsetEq : ∀ {ℓ o} {A : Set ℓ} {a a' : A} {P : A → Set o} → 
           .(p : P a) .(p' : P a') →
           a ≡ a' → a # p ≡ a' # p'
subsetEq p p' refl = refl

-- Shrinks a FinSetObj by one, removing the "first" element
shrinkObj : (A : FinSetObj) → ⦃ _ : Non⊥ A ⦄
            → FinSetObj
shrinkObj A@record{size = ℕ.suc size⁻} = record
  { Ty = Ty⁻
  ; size = size⁻
  ; toFin = toFinA⁻
  ; fromFin = fromFinA⁻
  ; inverseˡ = inverseˡA⁻
  ; inverseʳ = inverseʳA⁻
  }
  where
    open FinSetObj A

    Ty⁻ = Subset Ty (λ a → toFin a > zero {size⁻})

    toFinA⁻ : Ty⁻ → Fin size⁻
    toFinA⁻ (a # a>0) = lower' (toFin a) a>0

    fromFinA⁻ : Fin size⁻ → Ty⁻
    fromFinA⁻ i = fromFin (suc i) # si>0
      where
        si>0 : ℕ.suc ℕ.zero ℕ.≤ toℕ (toFin (fromFin (suc i)))
        si>0 rewrite inverseʳ {suc i} = ℕ.s≤s ℕ.z≤n
   
    -- TODO:
    postulate
      inverseˡA⁻ : ∀ {a⁻ : Ty⁻} →
                   fromFinA⁻ (toFinA⁻ a⁻) ≡ a⁻
      inverseʳA⁻ : ∀ {i : Fin size⁻} →
                   toFinA⁻ (fromFinA⁻ i) ≡ i


--    inverseˡA⁻ : {a⁻ : Ty⁻} →
--                 fromFinA⁻ (toFinA⁻ a⁻) ≡ a⁻
--    inverseˡA⁻ {a # a>0} = subsetEq {!!} a>0 (inverseˡ)
--    inverseˡA⁻ {a # a>0} with lower' (toFin a)
--    ... | i = {! !}
--    inverseˡA⁻ {a # a>0} = aux (toFin a) a>0 inverseˡ
--      where
--        aux : (w : Fin (ℕ.suc size⁻)) → .(w>0 : w > zero) →
--              fromFin w ≡ a →
--              fromFinA⁻ (lower' w w>0) ≡ (a # a>0)
--        aux (suc i) w>0 fromFin[w]≡a with lower' (suc i)
--        ... | _ = subsetEq {!!} a>0 fromFin[w]≡a

open FinSetObj

private
  variable
    A B C D : FinSetObj

infix 4 _⇒ᶠ_

_⇒ᶠ_ : Rel FinSetObj _
A ⇒ᶠ B = Vec (Fin (B .size)) (A .size)

private
  variable
    f g h : _ ⇒ᶠ _

FinSet : Category _ _ _
FinSet = record
  { Obj = FinSetObj
  ; _⇒_ = _⇒ᶠ_
  ; _≈_ = _≡_
  ; id = λ {A} → allFin (A .size)
  ; _∘_ = map ∘ lookup
  ; assoc = λ {A B C D f g h} → assoc A B C D f g h
  ; sym-assoc = λ {A B C D f g h} → sym (assoc A B C D f g h)
  ; identityˡ = λ {f = f} → identityˡ f
  ; identityʳ = λ {f = f} → map-lookup-allFin f
  ; identity² = λ {A} → identityˡ (allFin (A .size))
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = λ f≡h g≡i → cong₂ map (cong lookup f≡h) g≡i
  }
  where
    identityˡ : (xs : Vec (Fin n) m) → map (lookup (allFin n)) xs ≡ xs
    identityˡ [] = refl
    identityˡ (x ∷ xs) = cong₂ _∷_ (lookup-allFin x) (identityˡ xs)

    assoc : (A B C D : FinSetObj) (f : A ⇒ᶠ B) (g : B ⇒ᶠ C) (h : C ⇒ᶠ D) →
            map (lookup (map (lookup h) g)) f ≡
            map (lookup h) (map (lookup g) f)
    assoc A B C D [] g h = refl
    assoc A B C D (x ∷ f) g h =
      cong₂ _∷_ (lookup-map x (lookup h) g)
            (assoc (shrinkObj A) B C D f g h)
      where
      -- TODO: need to pattern match on size of A as well,
      -- but using 'with' messes up the recursive call
        postulate
          instance
            nonBotA : Non⊥ A

