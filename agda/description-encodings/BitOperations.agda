open import Agda.Builtin.Sigma
open import Data.Bool using (Bool; false; true)
open import Data.Nat
open import Data.List
  renaming ([] to []ₗ; _∷_ to _∷ₗ_; _++_ to _++ₗ_;
            replicate to replicateₗ)
open import Data.Vec
  renaming ([] to []ᵥ; _∷_ to _∷ᵥ_;   _++_ to _++ᵥ_;
            replicate to replicateᵥ)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

module BitOperations where
  
  module UnknownNat where

    -- Nats with an unknown element χ
    data ℕₓ : Set where
      Num : ℕ → ℕₓ
      χ : ℕₓ

    pattern 0χ = Num 0
    pattern 1χ = Num 1

    sucχ : ℕₓ → ℕₓ
    sucχ (Num n) = Num (suc n)
    sucχ χ = χ

    infixl 6 _⊕_

    _⊕_ : (𝓃 𝓂 : ℕₓ) → ℕₓ
    (Num n) ⊕ (Num m) = Num (n + m)
    (Num _) ⊕ χ = χ
    χ ⊕ _ = χ

    ⊕-identityˡ : {𝓃 : ℕₓ} → 0χ ⊕ 𝓃 ≡ 𝓃
    ⊕-identityˡ {𝓃 = Num n} = refl
    ⊕-identityˡ {𝓃 = χ} = refl

    ⊕-identityʳ : {𝓃 : ℕₓ} → 𝓃 ⊕ 0χ ≡ 𝓃
    ⊕-identityʳ {𝓃 = Num n} = cong Num (+-identityʳ)
      where
        +-identityʳ : {n : ℕ} → n + 0 ≡ n
        +-identityʳ {n = zero} = refl
        +-identityʳ {n = suc n} = cong suc (+-identityʳ {n})
    ⊕-identityʳ {𝓃 = χ} = refl

    infix 4 _≤ₓ_ _<ₓ_

    data _≤ₓ_ : Rel ℕₓ 0ℓ where
      n≤ₓm : ∀ {n m} → n ≤ m → (Num n) ≤ₓ (Num m)
      n≤ₓχ : ∀ {n} → (Num n) ≤ₓ χ
      χ≤ₓχ : χ ≤ₓ χ

    _<ₓ_ : Rel ℕₓ 0ℓ
    𝓃 <ₓ 𝓂 = (sucχ 𝓃) ≤ₓ 𝓂

  open UnknownNat
  
  private
    variable
      n m : ℕ
      𝓃 𝓂 : ℕₓ

  data Bit : Set where
    O : Bit
    I : Bit

  -- Little endian storage of bits (least significant first)
  𝔹_ : (𝓃 : ℕₓ) → Set
  𝔹 (Num n) = Vec Bit n
  𝔹 χ = List Bit

  -- Returns whether the addition caused an overflow (for fixed sized vectors)
  addI : 𝔹 𝓃 → Σ Bool (λ _overflow → 𝔹 𝓃)
  addI {𝓃 = (Num _)} []ᵥ = (true , []ᵥ)
  addI {𝓃 = χ} []ₗ = (false , I ∷ₗ []ₗ)
  addI {𝓃 = (Num _)} (O ∷ᵥ 𝕓) = (false , I ∷ᵥ 𝕓)
  addI {𝓃 = χ} (O ∷ₗ 𝕓) = (false , I ∷ₗ 𝕓)
  addI {𝓃 = (Num _)} (I ∷ᵥ 𝕓) with addI 𝕓
  ... | (overflow , 𝕓') = (overflow , O ∷ᵥ 𝕓')
  addI {𝓃 = χ} (I ∷ₗ 𝕓) with addI 𝕓
  ... | (_ , 𝕓') = (false , O ∷ₗ 𝕓')

  -- Right pad bit vectors with the given bit
  pad : Bit → (m : ℕ) → 𝔹 𝓃 → 𝔹 (𝓃 ⊕ (Num m))
  pad {𝓃 = (Num n)} b m 𝕓 = 𝕓 ++ᵥ (replicateᵥ m b)
  pad {𝓃 = χ} b m 𝕓 = 𝕓 ++ₗ (replicateₗ m b)

