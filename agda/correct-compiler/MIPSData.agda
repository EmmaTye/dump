open import Data.Nat

module MIPSData where

private
  variable
    n m : ℕ

module dataSection where

  data DataVal : Set where
    byte : DataVal 
    half : DataVal 
    word : DataVal 

  data DataType : Set where
    ∙_ : DataVal → DataType
    -- Array of size n of type value
    ∙_[_] : DataVal → (n : ℕ) → DataType
    -- Allocate a space of n bytes
    ∙space : (n : ℕ) → DataType

  -- de Bruijn indices for labels into data
  data DataLabel : ℕ → Set where
    here : DataLabel (suc n)
    there : DataLabel n → DataLabel (suc n)

open dataSection


