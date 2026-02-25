module FinUniverse where

record FinUniverse : Set₁ where
  constructor MkFinUniverse
  field
    Uꟳ : Set
    El : Uꟳ → Set

