open import Agda.Builtin.Sigma
  renaming (Σ to _×ᴰ_; _,_ to _,ᴰ_)

open import Data.Fin
  renaming (_+_ to _+F_)
open import Data.Fin.Patterns
open import Data.Nat
open import Data.Product
  using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; inspect; [_])

module clones where

  private
    variable
      n m p : ℕ
      T : ℕ → Set
      t s : T _

  record Clone (T : ℕ → Set) : Set where
    field
      η : Fin n → T n
      _>>=_ : T m → (Fin m → T n) → T n

      η-idl : {i : Fin n} {ϕ : Fin n → T n} →
              η i >>= ϕ ≡ ϕ i
      η-idr : {t : T n} →
              t >>= η ≡ t
      >>=-ass : {t : T n} {ϕ : Fin n → T m} {ψ : Fin m → T p} →
                (t >>= ϕ) >>= ψ ≡ t >>= (λ i → ϕ i >>= ψ)


