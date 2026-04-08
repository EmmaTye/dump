open Agda.Primitive
open import Axiom.Extensionality.Propositional 
  using (Extensionality)
open import Function.Base
  using (_∘_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; inspect; [_])

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
        𝓁 𝓁₁ 𝓁₂ : Level
        A B C D : Set
        a a' : A
        b b' : B
        c c' : C
        d d' : D

    _⇛_ : Set → Set → Set
    A ⇛ B = A → B

    postulate
      ext : ∀ {𝓁₁ 𝓁₂} → Extensionality 𝓁₁ 𝓁₂
  
    𝟘⇛a : (𝟘 ⇛ A) ≅ 𝟙
    𝟘⇛a {A} = record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : (𝟘 → A) → 𝟙
        ⇒ f = tt

        _⇐ : 𝟙 → (𝟘 → A)
        tt ⇐ = λ ()

        idl : ∀ {f : 𝟘 → A} → ⇒ f ⇐ ≡ f
        idl = ext (λ ())

        idr : ∀ {𝟙x : 𝟙} → ⇒ (𝟙x ⇐) ≡ 𝟙x
        idr {tt} = refl

    a⇛𝟘 : (a : A) → (A ⇛ 𝟘) ≅ 𝟘
    a⇛𝟘 {A} a = record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : (A → 𝟘) → 𝟘
        ⇒ f = f a
        
        _⇐ : 𝟘 → (A → 𝟘)
        () ⇐

        idl : ∀ {f : A → 𝟘} → ⇒ f ⇐ ≡ f
        idl {f} = ext (λ a' → 𝟘-elim (f a'))

        idr : ∀ {𝟘x : 𝟘} → ⇒ (𝟘x ⇐) ≡ 𝟘x
        idr {()}

    𝟙⇛a : (𝟙 ⇛ A) ≅ A
    𝟙⇛a {A} = record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = ext idl-ext;
        idr = refl
      } where
        ⇒ : (𝟙 → A) → A
        ⇒ f = f tt

        _⇐ : A → (𝟙 → A)
        (a ⇐) tt = a

        idl-ext : {f : 𝟙 → A} → (x : 𝟙) → (⇒ f ⇐) x ≡ f x
        idl-ext tt = refl

    a⇛𝟙 : (A ⇛ 𝟙) ≅ 𝟙
    a⇛𝟙 {A} = record {
      ⇒ = ⇒;
      _⇐ = _⇐;
      idl = ext id-ext;
      idr = idr
      } where
        ⇒ : (A → 𝟙) → 𝟙
        ⇒ f = tt

        _⇐ : 𝟙 → (A → 𝟙)
        tt ⇐ = λ a → tt

        id-ext : {f : A ⇛ 𝟙} → (a : A) → (⇒ f ⇐) a ≡ f a
        id-ext {f} a with f a
        ... | tt = refl

        idr : ∀ {𝟙x : 𝟙} → ⇒ (𝟙x ⇐) ≡ 𝟙x
        idr {tt} = refl

    ＋⋆⇛ : ((A ＋ B) ⇛ C) ≅ ((A ⇛ C) ⋆ (B ⇛ C))
    ＋⋆⇛ {A} {B} {C} = record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = ext idl-ext;
        idr = idr 
      } where
        ⇒ : ((A ＋ B) → C) → (A → C) ⋆ (B → C)
        ⇒ f = ((λ a → f (inj₁ a)) , (λ b → f (inj₂ b)))
        
        _⇐ : (A → C) ⋆ (B → C) → ((A ＋ B) → C)
        (g₁ , g₂) ⇐ = f where
          f : A ＋ B → C
          f (inj₁ a) = g₁ a
          f (inj₂ b) = g₂ b

        idl-ext : {f : (A ＋ B) → C} → (ab : A ＋ B) →
                 (⇒ f ⇐) ab ≡ f ab
        idl-ext (inj₁ ab) = refl
        idl-ext (inj₂ ab) = refl

        idr : {g : (A → C) ⋆ (B → C)} → ⇒ (g ⇐) ≡ g
        idr {g₁ , g₂} = refl

    ⋆⇛ : (A ⇛ (B ⋆ C)) ≅ ((A ⇛ B) ⋆ (A ⇛ C))
    ⋆⇛ {A} {B} {C} = record {
      ⇒ = ⇒;
      _⇐ =  _⇐;
      idl = ext idl-ext;
      idr = idr
      } where
        ⇒ : (A → (B ⋆ C)) → ((A → B) ⋆ (A → C))
        ⇒ f = ((π₁ ∘ f) , (π₂ ∘ f))

        _⇐ : ((A → B) ⋆ (A → C)) → (A → (B ⋆ C))
        ((g₁ , g₂) ⇐) a = ((g₁ a) , (g₂ a))

        idl-ext : {f : A → (B ⋆ C)} → (a : A) →
                  (⇒ f ⇐) a ≡ f a
        idl-ext {f} a with f a
        ... | (b , c) = refl

        idr : ∀ {g : (A → B) ⋆ (A → C)} → ⇒ (g ⇐) ≡ g
        idr {g₁ , g₂} = refl

    curry : ((A ⋆ B) ⇛ C) ≅ (A ⇛ (B ⇛ C))
    curry {A} {B} {C} = record {
      ⇒ = ⇒;
      _⇐ = _⇐;
      idl = ext idl-ext;
      idr = λ {g} → ext (λ a → ext (idr-ext {g} a))
      } where
        ⇒ : ((A ⋆ B) → C) → (A → (B → C))
        ⇒ f a b = f (a , b)

        _⇐ : (A → (B → C)) → ((A ⋆ B) → C)
        (g ⇐) (a , b) = g a b

        idl-ext : {f : (A ⋆ B) → C} → (ab : A ⋆ B) →
                  (⇒ f ⇐) ab ≡ f ab
        idl-ext {f} (a , b) = refl

        idr-ext : {g : A → B → C} → (a : A) → (b : B) →
                  (⇒ (g ⇐)) a b ≡ g a b
        idr-ext {g} a b = refl

    -- ≅ and ⇛ laws
    ⇛≅contra : A ≅ B →
               (A ⇛ C) ≅ (B ⇛ C)
    ⇛≅contra {A} {B} {C}
             record {
               ⇒ = a→b;
               _⇐ = b→a;
               idl = ida→b;
               idr = idb→a
             } =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = ext idl-ext;
        idr = ext idr-ext
      } where
        ⇒ : (A → C) → (B → C)
        ⇒ f = f ∘ b→a

        _⇐ : (B → C) → (A → C)
        g ⇐ = g ∘ a→b

        idl-ext : {f : A → C} → (a : A) → (⇒ f ⇐) a ≡ f a
        idl-ext {f} a = cong f ida→b

        idr-ext : {g : B → C} → (b : B) → (⇒ (g ⇐)) b ≡ g b
        idr-ext {g} b = cong g idb→a

    ⇛≅cov : ∀ {A B C} → B ≅ C →
            (A ⇛ B) ≅ (A ⇛ C)
    ⇛≅cov {A} {B} {C}
          record {
            ⇒ = b→c;
            _⇐ = c→b;
            idl = idb→c;
            idr = idc→b
          } =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = ext idl-ext;
        idr = ext idr-ext 
      } where
        ⇒ : (A → B) → (A → C)
        ⇒ f = b→c ∘ f

        _⇐ : (A → C) → (A → B)
        g ⇐ = c→b ∘ g

        idl-ext : {f : A → B} → (a : A) → (⇒ f ⇐) a ≡ f a
        idl-ext _ = idb→c

        idr-ext : {g : A → C} → (a : A) → (⇒ (g ⇐)) a ≡ g a
        idr-ext _ = idc→b

    -- ⊑ and ⇛ laws
    ⇛⊑contra : ∀ {A B C} → B ⊑ A →
               (A ⇛ C) ⊑ (B ⇛ C)
    ⇛⊑contra {A} {B} {C}
             record {
               ⇒ = b→a;
               _⇐ = a→mb;
               idl = idb→a;
               idr = ida→mb
             } =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = ?;
        idr = ?
      } where
        ⇒ : (A → C) → (B → C)
        ⇒ f = f ∘ b→a

        -- TODO: I don't think this works
        -- we can prove
        -- _⇐ : (B → C) → (A → Maybe C)
        -- (g ⇐) a = map g a→mb
        -- but that's not what we want
        -- Maybe we need a new notion of partial isomorphism
        -- between functions...
        _⇐ : (B → C) → Maybe (A → C)
        g ⇐ = ?

    ⇛⊑cov : ∀ {A B} → B ⊑ C →
            (A ⇛ B) ⊑ (A ⇛ C)

  FunModel : FunTT
  FunModel = record { FunModel }

