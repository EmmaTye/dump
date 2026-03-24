open import Agda.Builtin.Sigma
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Descriptions

module Encodings where

variable
  t𝒟 : TaggedDescription

record Encoding : Set₁ where
  field
    Target : Set -- Target type for encoding, e.g. Bit-vector, JSON, etc.
    -- TODO: Add lenses for Enc
    Enc : Target → (t𝒟 : TaggedDescription) → Set -- Subset of Target which encodes the given description
    NEnc : (t𝒟 : TaggedDescription) → Set -- Contains information about a failed decoding of the Target into data' t𝒟
    enc : μ⁺ t𝒟 → Σ Target (λ t → Enc t t𝒟)
    dec : Target → μ⁺ t𝒟 ⊎ NEnc t𝒟

    -- dec recovers encoded data exactly
    enc-dec-η : ∀ {d : μ⁺ t𝒟} → dec (fst (enc d)) ≡ inj₁ d
    -- TODO: concept of normalised serialisation? like removing padding etc.
    dec-enc-η : ∀ {t : Target} {d : μ⁺ t𝒟} → 
                dec t ≡ inj₁ d →
                fst (enc d) ≡ t

