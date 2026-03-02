open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat

open import Data.Sum
open import Data.Vec

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Descriptions

module Encodings where

record Encoding : Set₁ where
  field
    Target : Set -- Target type for encoding, e.g. Bit-vector, JSON, etc.
    -- TODO: Add lenses for Enc
    Enc : (t𝒟 : TaggedDescription) → Set -- Subset of Target which encodes the given description
    NEnc : (t𝒟 : TaggedDescription) → Set -- Contains information about a failed decoding of the Target into data' t𝒟
    inj : ∀ {t𝒟 : TaggedDescription} → Enc t𝒟 → Target
    enc : ∀ {t𝒟 : TaggedDescription} → μ⁺ t𝒟 → Enc t𝒟
    dec : ∀ {t𝒟 : TaggedDescription} →
          Target → μ⁺ t𝒟 ⊎ NEnc t𝒟

    -- Laws
    -- inj is indeed injective
    inj↪ : ∀ {t𝒟 : TaggedDescription} {e₁ e₂ : Enc t𝒟} →
           inj e₁ ≡ inj e₂ → e₁ ≡ e₂
    -- dec recovers encoded data exactly
    enc-dec-η : ∀ {t𝒟 : TaggedDescription} {d : μ⁺ t𝒟} →
                dec (inj (enc d))
                ≡ inj₁ d

