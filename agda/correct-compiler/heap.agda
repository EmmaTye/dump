{-# OPTIONS --safe #-}

open import Data.Nat

module heap where

-- TODO: use words instead? Or keep as Nats since these are "virtual" heaps anyway
Location = ℕ

-- A heap is a partial map from locations to values
-- TODO: maybe use Data.Tree.AVL.IndexedMap? Or something similar where we ensure locations are ordered and unique in a Heap
data Heap (Value : Set) : Set where
  ϵ : Heap Value
  _↦_-,_ : Location → Value → Heap Value

