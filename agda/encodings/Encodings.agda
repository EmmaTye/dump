
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
    Enc : (t𝒟 : TaggedDescription) → Set -- Subset of Target which encodes the given description
    NEnc : (t𝒟 : TaggedDescription) → Set -- Contains information about a failed decoding of the Target into data' t𝒟
    inj : Enc t𝒟 → Target
    enc : μ⁺ t𝒟 → Enc t𝒟
    dec : Target → μ⁺ t𝒟 ⊎ NEnc t𝒟

    -- Laws
    -- inj is indeed injective
    inj↪ : {e₁ e₂ : Enc t𝒟} →
           inj e₁ ≡ inj e₂ → e₁ ≡ e₂
    -- dec recovers encoded data exactly
    enc-dec-η : {d : μ⁺ t𝒟} →
                dec (inj (enc d)) ≡ inj₁ d

