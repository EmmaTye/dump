open import BaseModel
open import BaseTT
open import FunTT

module FunModel where

  module FunModel where
    open import BaseModel
    open BaseTys
    open PartialIsos

    private
      variable
        A B C D : Set
        a a' : A
        b b' : B
        c c' : C
        d d' : D

    _⇛_ : Set → Set → Set
  
    𝟘⇛a : (𝟘 ⇛ A) ≅ 𝟙
    a⇛𝟘 : (A ⇛ 𝟘) ≅ 𝟘

    𝟙⇛a : (𝟙 ⇛ A) ≅ A
    a⇛𝟙 : (A ⇛ 𝟙) ≅ 𝟙

    ＋⋆⇛ : ((A ＋ B) ⇛ C) ≅ ((A ⇛ C) ⋆ (B ⇛ C))
    ⋆⇛ : (A ⇛ (B ⋆ C)) ≅ ((A ⇛ C) ⋆ (B ⇛ C))
    curry : ((A ⋆ B) ⇛ C) ≅ (A ⇛ (B ⇛ C))

    -- ≅ and ⇛ laws
    ⇛≅contra : A ≅ B →
               (A ⇛ C) ≅ (B ⇛ C)
    ⇛≅cov : B ≅ C →
            (A ⇛ B) ≅ (A ⇛ C)

    -- ⊑ and ⇛ laws
    ⇛⊑contra : B ⊑ A →
               (A ⇛ C) ⊑ (B ⇛ C)
    ⇛⊑cov : B ⊑ C →
            (A ⇛ B) ⊑ (A ⇛ C)

  FunModel : FunTT
  FunModel = record { FunModel }

