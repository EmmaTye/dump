open import Function.Base
  using (_∘_)
open import Data.Maybe
open import Data.Maybe.Properties
  using (just-injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; inspect; [_])

open import BaseTT

module BaseModel where

  private
    variable
      A B C D : Set
      a a' : A
      b b' : B
      c c' : C
      d d' : D

  -- TODO: this isn't defined in Data.Maybe that I can find...
  private
    _<=<_ : (B → Maybe C) → (A → Maybe B) → (A → Maybe C)
    g <=< f = λ a → f a >>= g

  module BaseTys where
    
    data 𝟘 : Set where

    𝟘-elim : ∀ {A : Set} → 𝟘 → A
    𝟘-elim ()

    data 𝟙 : Set where
      tt : 𝟙

    data _＋_ (A B : Set) : Set where
      inj₁ : A → A ＋ B
      inj₂ : B → A ＋ B
    
    infixl 10 _＋_

    data _⋆_ (A B : Set) : Set where
      _,_ : A → B → A ⋆ B
    
    infixl 9 _⋆_
    infixl 9 _,_

    π₁ : A ⋆ B → A
    π₁ (a , b) = a

    π₂ : A ⋆ B → B
    π₂ (a , b) = b

    data Sum₃ (A₁ A₂ A₃ : Set) : Set where
      inj₁ : A₁ → Sum₃ A₁ A₂ A₃
      inj₂ : A₂ → Sum₃ A₁ A₂ A₃
      inj₃ : A₃ → Sum₃ A₁ A₂ A₃
  
    data Sum₄ (A₁ A₂ A₃ A₄ : Set) : Set where
      inj₁ : A₁ → Sum₄ A₁ A₂ A₃ A₄
      inj₂ : A₂ → Sum₄ A₁ A₂ A₃ A₄
      inj₃ : A₃ → Sum₄ A₁ A₂ A₃ A₄
      inj₄ : A₄ → Sum₄ A₁ A₂ A₃ A₄
  
    data Prod₃ (A₁ A₂ A₃ : Set) : Set where
      prod₃ : A₁ → A₂ → A₃ → Prod₃ A₁ A₂ A₃
    
    data Prod₄ (A₁ A₂ A₃ A₄ : Set) : Set where
      prod₄ : A₁ → A₂ → A₃ → A₄ → Prod₄ A₁ A₂ A₃ A₄
  
  BaseTys : BaseTypes
  BaseTys = record {
      BaseTys;
      Ty = Set;
      Tm = λ A → A
    }

  module PartialIsos where

    record _≅_ (A B : Set) : Set where
      field
        ⇒ : A → B
        _⇐ : B → A
        idl : ∀ {a : A} →
              (⇒ a) ⇐ ≡ a
        idr : ∀ {b : B} →
              ⇒ (b ⇐) ≡ b

    record _⊑_ (A B : Set) : Set where
      field
        ⇒ : A → B
        _⇐ : B → Maybe A
        idl : ∀ {a : A} →
              (⇒ a) ⇐ ≡ just a
        idr : ∀ {a : A} {b : B} →
              (b ⇐) ≡ just a →
              ⇒ a ≡ b

    refl≅ : A ≅ A
    refl≅ = record {
        ⇒ = λ a → a;
        _⇐ = λ a → a;
        idl = refl;
        idr = refl
      }

    sym≅ : A ≅ B → B ≅ A
    sym≅ record { ⇒ = _⇐; 
                  _⇐ = ⇒; 
                  idl = idr; 
                  idr = idl } =
      -- TODO: is there some OCaml-style record assignment where if you're assigning vars the same name as the fields you can omit the "= var" repetition?
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      }

    trans≅ : A ≅ B → B ≅ C → A ≅ C
    trans≅ record { ⇒ = a→b; 
                    _⇐ = b→a; 
                    idl = ida→b; 
                    idr = idb→a }
           record { ⇒ = b→c; 
                    _⇐ = c→b; 
                    idl = idb→c; 
                    idr = idc→b } =
      record {
        ⇒ = b→c ∘ a→b;
        _⇐ = b→a ∘ c→b;
        idl = trans (cong b→a idb→c) ida→b;
        idr = trans (cong b→c idb→a) idc→b
      }

    refl⊑ : A ⊑ A
    refl⊑ = record {
        ⇒ = λ a → a;
        _⇐ = λ a → just a;
        idl = refl;
        idr = λ b⇐≡a → sym (just-injective b⇐≡a)
      }

    trans⊑ : A ⊑ B → B ⊑ C → A ⊑ C
    trans⊑ {A} {B} {C}
           record { ⇒ = a→b;
                    _⇐ = b→ma;
                    idl = ida→b;
                    idr = idb→ma }
           record { ⇒ = b→c;
                    _⇐ = c→mb;
                    idl = idb→c;
                    idr = idc→mb } =
      record {
        ⇒ = a→c;
        _⇐ = c→ma;
        idl = idl;
        idr = idr
      }
      where
        a→c = b→c ∘ a→b
        c→ma = b→ma <=< c→mb

        idl : ∀ {a : A} → c→ma (a→c a) ≡ just a
        idl = trans (cong (_>>= b→ma) idb→c) ida→b

        idr : ∀ {a : A} {c : C} →
              c→ma c ≡ just a →
              a→c a ≡ c
        idr {a} {c} _ with c→mb c | inspect c→mb c
        ... | just b | _ with b→ma b | inspect b→ma b
        idr {a} {c} refl | just b | [ c→mbc≡justb ] | just a | [ b→mab≡justa ] =
          let
            idb→ma = idb→ma b→mab≡justa
            idc→mb = idc→mb c→mbc≡justb
          in
          trans (cong b→c idb→ma) idc→mb

  PI : PartialIso (BaseTypes.Ty BaseTys)
  PI = record { PartialIsos }

  module BaseModel where
    open BaseTys
    open PartialIsos
    
    ＋idl : (𝟘 ＋ A) ≅ A
    ＋idl {A} = record { 
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = refl
      }
      where
        ⇒ : (𝟘 ＋ A) → A
        ⇒ (inj₂ a) = a

        _⇐ : A → (𝟘 ＋ A)
        a ⇐ = inj₂ a

        idl : {𝟘a : 𝟘 ＋ A} → ⇒ 𝟘a ⇐ ≡ 𝟘a
        idl {𝟘a = inj₂ a} = refl

    ＋comm : (A ＋ B) ≅ (B ＋ A)
    ＋comm {A} {B} = 
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      }
      where
        ⇒ : (A ＋ B) → (B ＋ A)
        ⇒ (inj₁ a) = inj₂ a
        ⇒ (inj₂ b) = inj₁ b

        _⇐ : (B ＋ A) → (A ＋ B)
        (inj₁ b) ⇐ = inj₂ b
        (inj₂ a) ⇐ = inj₁ a

        idl : {ab : A ＋ B} → ⇒ ab ⇐ ≡ ab
        idl {ab = inj₁ a} = refl
        idl {ab = inj₂ b} = refl

        idr : {ba : B ＋ A} → ⇒ (ba ⇐) ≡ ba
        idr {ba = inj₁ b} = refl
        idr {ba = inj₂ a} = refl

    ＋ass : ((A ＋ B) ＋ C) ≅ (A ＋ (B ＋ C))
    ＋ass {A} {B} {C} =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : ((A ＋ B) ＋ C) → (A ＋ (B ＋ C))
        ⇒ (inj₁ (inj₁ a)) = inj₁ a
        ⇒ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
        ⇒ (inj₂ c) = inj₂ (inj₂ c)

        _⇐ : (A ＋ (B ＋ C)) → ((A ＋ B) ＋ C)
        inj₁ a ⇐ = inj₁ (inj₁ a)
        inj₂ (inj₁ b) ⇐ = inj₁ (inj₂ b)
        inj₂ (inj₂ c) ⇐ = inj₂ c

        idl : ∀ {abc : (A ＋ B) ＋ C} → ⇒ abc ⇐ ≡ abc
        idl {inj₁ (inj₁ a)} = refl
        idl {inj₁ (inj₂ b)} = refl
        idl {inj₂ c} = refl

        idr : ∀ {abc : A ＋ (B ＋ C)} → ⇒ (abc ⇐) ≡ abc
        idr {inj₁ a} = refl
        idr {inj₂ (inj₁ b)} = refl
        idr {inj₂ (inj₂ c)} = refl

    ⋆idl : (𝟙 ⋆ A) ≅ A
    ⋆idl {A} = record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = refl
      }
      where
        ⇒ : (𝟙 ⋆ A) → A
        ⇒ (_ , a) = a

        _⇐ : A → (𝟙 ⋆ A)
        a ⇐ = (tt , a)

        idl : ∀ {𝟙a : 𝟙 ⋆ A} → ⇒ 𝟙a ⇐ ≡ 𝟙a
        idl {𝟙a = (tt , a)} = refl

    ⋆comm : (A ⋆ B) ≅ (B ⋆ A)
    ⋆comm {A} {B} = record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      }
      where
        ⇒ : (A ⋆ B) → (B ⋆ A)
        ⇒ (a , b) = (b , a)

        _⇐ : (B ⋆ A) → (A ⋆ B)
        _⇐ (b , a) = (a , b)

        idl : ∀ {ab : A ⋆ B} → ⇒ ab ⇐ ≡ ab
        idl {ab = (a , b)} = refl

        idr : ∀ {ba : B ⋆ A} → ⇒ (ba ⇐) ≡ ba
        idr {ba = (b , a)} = refl

    ⋆ass : ((A ⋆ B) ⋆ C) ≅ (A ⋆ (B ⋆ C))
    ⋆ass {A} {B} {C} =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : (A ⋆ B) ⋆ C → A ⋆ (B ⋆ C)
        ⇒ ((a , b) , c) = a , (b , c)

        _⇐ : A ⋆ (B ⋆ C) → (A ⋆ B) ⋆ C
        (a , (b , c)) ⇐ = ((a , b) , c)

        idl : ∀ {abc : (A ⋆ B) ⋆ C} →
              ⇒ abc ⇐ ≡ abc
        idl {(a , b) , c} = refl

        idr : ∀ {abc : A ⋆ (B ⋆ C)} →
              ⇒ (abc ⇐) ≡ abc
        idr {a , (b , c)} = refl

    ⋆absorbl : (𝟘 ⋆ A) ≅ 𝟘
    ⋆absorbl {A} =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : 𝟘 ⋆ A → 𝟘
        ⇒ = 𝟘-elim ∘ π₁

        _⇐ : 𝟘 → 𝟘 ⋆ A
        _⇐ ()

        idl : ∀ {𝟘a : 𝟘 ⋆ A} → ⇒ 𝟘a ⇐ ≡ 𝟘a
        idl {𝟘a} = 𝟘-elim (π₁ 𝟘a)

        idr : ∀ {𝟘x : 𝟘} → ⇒ (𝟘x ⇐) ≡ 𝟘x
        idr {()}

    ⋆＋dist : (A ⋆ (B ＋ C)) ≅ ((A ⋆ B) ＋ (A ⋆ C))
    ⋆＋dist {A} {B} {C} = 
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      }
      where
        ⇒ : (A ⋆ (B ＋ C)) → ((A ⋆ B) ＋ (A ⋆ C))
        ⇒ (a , (inj₁ b)) = 
          inj₁ (a , b)
        ⇒ (a , (inj₂ c)) = 
          inj₂ (a , c)

        _⇐ : ((A ⋆ B) ＋ (A ⋆ C)) → (A ⋆ (B ＋ C))
        (inj₁ (a , b)) ⇐ =
          (a , (inj₁ b))
        (inj₂ (a , c)) ⇐ =
          (a , (inj₂ c))

        idl : ∀ {abc : (A ⋆ (B ＋ C))} → ⇒ abc ⇐ ≡ abc
        idl {abc = (a , (inj₁ b))} = refl
        idl {abc = (a , (inj₂ c))} = refl

        idr : ∀ {abc : ((A ⋆ B) ＋ (A ⋆ C))} → ⇒ (abc ⇐) ≡ abc
        idr {abc = (inj₁ (a , b))} = refl
        idr {abc = (inj₂ (a , c))} = refl

    ＋Sum₃ : ((A ＋ B) ＋ C) ≅ Sum₃ A B C
    ＋Sum₃ {A} {B} {C} =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : ((A ＋ B) ＋ C) → Sum₃ A B C
        ⇒ (inj₁ (inj₁ a)) = inj₁ a
        ⇒ (inj₁ (inj₂ b)) = inj₂ b
        ⇒ (inj₂ c) = inj₃ c

        _⇐ : Sum₃ A B C → ((A ＋ B) ＋ C)
        inj₁ a ⇐ = inj₁ (inj₁ a)
        inj₂ b ⇐ = inj₁ (inj₂ b)
        inj₃ c ⇐ = inj₂ c

        idl : ∀ {abc : (A ＋ B) ＋ C} →
              ⇒ abc ⇐ ≡ abc
        idl {inj₁ (inj₁ a)} = refl
        idl {inj₁ (inj₂ b)} = refl
        idl {inj₂ c} = refl

        idr : ∀ {abc : Sum₃ A B C} →
              ⇒ (abc ⇐) ≡ abc
        idr {inj₁ a} = refl
        idr {inj₂ b} = refl
        idr {inj₃ c} = refl

    ＋Sum₄ : (((A ＋ B) ＋ C) ＋ D) ≅ Sum₄ A B C D
    ＋Sum₄ {A} {B} {C} {D} =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : (((A ＋ B) ＋ C) ＋ D) → Sum₄ A B C D
        ⇒ (inj₁ (inj₁ (inj₁ a))) = inj₁ a
        ⇒ (inj₁ (inj₁ (inj₂ b))) = inj₂ b
        ⇒ (inj₁ (inj₂ c)) = inj₃ c
        ⇒ (inj₂ d) = inj₄ d

        _⇐ : Sum₄ A B C D → (((A ＋ B) ＋ C) ＋ D)
        inj₁ a ⇐ = inj₁ (inj₁ (inj₁ a))
        inj₂ b ⇐ = inj₁ (inj₁ (inj₂ b))
        inj₃ c ⇐ = inj₁ (inj₂ c)
        inj₄ d ⇐ = inj₂ d

        idl : ∀ {abcd : ((A ＋ B) ＋ C) ＋ D} →
              ⇒ abcd ⇐ ≡ abcd
        idl {inj₁ (inj₁ (inj₁ a))} = refl
        idl {inj₁ (inj₁ (inj₂ b))} = refl
        idl {inj₁ (inj₂ c)} = refl
        idl {inj₂ d} = refl

        idr : ∀ {abcd : Sum₄ A B C D} →
              ⇒ (abcd ⇐) ≡ abcd
        idr {inj₁ a} = refl
        idr {inj₂ b} = refl
        idr {inj₃ c} = refl
        idr {inj₄ c} = refl

    ⋆Prod₃ : ((A ⋆ B) ⋆ C) ≅ Prod₃ A B C
    ⋆Prod₃ {A} {B} {C} =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : ((A ⋆ B) ⋆ C) → Prod₃ A B C
        ⇒ ((a , b) , c) = prod₃ a b c

        _⇐ : Prod₃ A B C → ((A ⋆ B) ⋆ C)
        (prod₃ a b c) ⇐ = (a , b) , c

        idl : ∀ {abc : (A ⋆ B) ⋆ C} →
              ⇒ abc ⇐ ≡ abc
        idl {(a , b) , c} = refl

        idr : ∀ {abc : Prod₃ A B C} →
              ⇒ (abc ⇐) ≡ abc
        idr {prod₃ a b c} = refl

    ⋆Prod₄ :  (((A ⋆ B) ⋆ C) ⋆ D) ≅ Prod₄ A B C D
    ⋆Prod₄ {A} {B} {C} {D} =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : (((A ⋆ B) ⋆ C) ⋆ D) → Prod₄ A B C D
        ⇒ (((a , b) , c) , d) = prod₄ a b c d

        _⇐ : Prod₄ A B C D → (((A ⋆ B) ⋆ C) ⋆ D)
        (prod₄ a b c d) ⇐ = ((a , b) , c) , d

        idl : ∀ {abcd : ((A ⋆ B) ⋆ C) ⋆ D} →
              ⇒ abcd ⇐ ≡ abcd
        idl {((a , b) , c) , d} = refl

        idr : ∀ {abcd : Prod₄ A B C D} →
              ⇒ (abcd ⇐) ≡ abcd
        idr {prod₄ a b c d} = refl

    ＋≅l : A ≅ B → (A ＋ C) ≅ (B ＋ C)
    ＋≅l {A} {B} {C}
         record { ⇒ = a→b;
                  _⇐ = b→a;
                  idl = ida→b;
                  idr = idb→a } =
       record {
         ⇒ = ⇒;
         _⇐ = _⇐;
         idl = idl;
         idr = idr
       } where
         ⇒ : A ＋ C → B ＋ C
         ⇒ (inj₁ a) = inj₁ (a→b a)
         ⇒ (inj₂ c) = inj₂ c

         _⇐ : B ＋ C → A ＋ C
         (inj₁ b) ⇐ = inj₁ (b→a b)
         (inj₂ c) ⇐ = inj₂ c

         idl : ∀ {ac : A ＋ C} →
                ⇒ ac ⇐ ≡ ac
         idl {inj₁ a} = cong inj₁ ida→b
         idl {inj₂ c} = refl

         idr : ∀ {bc : B ＋ C} →
                ⇒ (bc ⇐) ≡ bc
         idr {inj₁ b} = cong inj₁ idb→a
         idr {inj₂ c} = refl

    ⋆≅l : A ≅ B → (A ⋆ C) ≅ (B ⋆ C)
    ⋆≅l {A} {B} {C}
        record { ⇒ = a→b;
                 _⇐ = b→a;
                 idl = ida→b;
                 idr = idb→a } =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr 
      } where
        ⇒ : A ⋆ C → B ⋆ C
        ⇒ (a , c) = ((a→b a) , c)

        _⇐ : B ⋆ C → A ⋆ C
        (b , c) ⇐ = ((b→a b) , c)

        idl : ∀ {ac : A ⋆ C} →
              ⇒ ac ⇐ ≡ ac
        idl {a , c} = cong (_, c) (ida→b)

        idr : ∀ {bc : B ⋆ C} →
              ⇒ (bc ⇐) ≡ bc
        idr {b , c} = cong (_, c) (idb→a)

    transportl : A ≅ B → A ⊑ C → B ⊑ C
    transportl {A} {B} {C} 
               record { ⇒ = a→b;
                        _⇐ = b→a;
                        idl = ida→b;
                        idr = idb→a } 
               record { ⇒ = a→c;
                        _⇐ = c→ma;
                        idl = ida→c;
                        idr = idc→ma } =
      record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      }
      where
        ⇒ = a→c ∘ b→a
        _⇐ = λ c → map a→b (c→ma c)

        idl : ∀ {b : B} → ⇒ b ⇐ ≡ just b
        idl = trans (cong (map (a→b)) ida→c) (cong just idb→a)

        idr : ∀ {b : B} {c : C} →
              (c ⇐) ≡ just b → ⇒ b ≡ c
        idr {b} {c} is-just with c→ma c | inspect c→ma c
        ... | just a | [ c→mac≡justa ] with a→b a | inspect a→b a
        idr {b} {c} refl | just a | [ c→mac≡justa ] | b | [ a→ba≡b ] =
          let
            a→ca≡c = idc→ma c→mac≡justa
          in
          trans (cong (a→c ∘ b→a) (sym a→ba≡b)) (trans (cong a→c ida→b) a→ca≡c)

    transportr : A ≅ B → C ⊑ A → C ⊑ B
    transportr {A} {B} {C} 
               record { ⇒ = a→b;
                        _⇐ = b→a;
                        idl = ida→b;
                        idr = idb→a }
               record { ⇒ = c→a;
                        _⇐ = a→mc;
                        idl = idc→a;
                        idr = ida→mc } =
      record {
        ⇒ = c→b;
        _⇐ = b→mc;
        idl = idl;
        idr = idr
      } where
          c→b = a→b ∘ c→a
          b→mc = a→mc ∘ b→a

          idl : ∀ {c : C} → b→mc (c→b c) ≡ just c
          idl = trans (cong a→mc ida→b) idc→a

          idr : ∀ {c : C} {b : B} →
                b→mc b ≡ just c →
                c→b c ≡ b
          idr {c} {b} is-just with b→a b | inspect b→a b
          ... | a | [ b→ab≡a ] =
            let
              c→ac≡a = ida→mc is-just
              a→ba≡b = trans (cong a→b (sym b→ab≡a)) idb→a
            in
            trans (cong a→b c→ac≡a) a→ba≡b

    ＋⊑l : A ⊑ B → (A ＋ C) ⊑ (B ＋ C)
    ＋⊑l {A} {B} {C} 
         record { ⇒ = a→b;
                  _⇐ = b→ma;
                  idl = ida→b;
                  idr = idb→ma } =
      record {
        ⇒ = ac→bc;
        _⇐ = bc→mac;
        idl = idl;
        idr = idr
      } where
        ac→bc : A ＋ C → B ＋ C
        ac→bc (inj₁ a) = inj₁ (a→b a)
        ac→bc (inj₂ c) = inj₂ c

        bc→mac : B ＋ C → Maybe (A ＋ C)
        bc→mac (inj₁ b) = map inj₁ (b→ma b)
        bc→mac (inj₂ c) = just (inj₂ c)

        idl : ∀ {ac : A ＋ C} → bc→mac (ac→bc ac) ≡ just ac
        idl {inj₁ a} = cong (map inj₁) ida→b
        idl {inj₂ c} = refl

        idr : ∀ {ac : A ＋ C} {bc : B ＋ C} →
              bc→mac bc ≡ just ac →
              ac→bc ac ≡ bc
        idr {ac} {inj₁ b} is-just with b→ma b | inspect b→ma b
        idr {ac} {inj₁ b} refl | just a | [ b→mab≡justa ] =
          cong inj₁ (idb→ma b→mab≡justa)
        idr {ac} {inj₂ c} refl = refl

    ⋆⊑l : A ⊑ B → (A ⋆ C) ⊑ (B ⋆ C)
    ⋆⊑l {A} {B} {C} 
         record { ⇒ = a→b;
                  _⇐ = b→ma;
                  idl = ida→b;
                  idr = idb→ma } =
      record {
        ⇒ = ac→bc;
        _⇐ = bc→mac;
        idl = idl;
        idr = idr
      } where
        ac→bc : A ⋆ C → B ⋆ C
        ac→bc (a , c) = (a→b a) , c

        bc→mac : B ⋆ C → Maybe (A ⋆ C)
        bc→mac (b , c) = map (λ a → a , c) (b→ma b)

        idl : ∀ {ac : A ⋆ C} → bc→mac (ac→bc ac) ≡ just ac
        idl {a , c} = cong (map (λ a → a , c)) ida→b

        idr : ∀ {ac : A ⋆ C} {bc : B ⋆ C} →
              bc→mac bc ≡ just ac →
              ac→bc ac ≡ bc
        idr {bc = b , c} _ with b→ma b | inspect b→ma b
        idr {ac = a , c} refl | just a | [ b→mab≡justa ] =
          let
            a→ba≡b = idb→ma b→mab≡justa
          in
          cong (λ b → b , c) a→ba≡b

    ＋extendl : A ⊑ (A ＋ B)
    ＋extendl {A} {B} = record {
        ⇒ = ⇒;
        _⇐ = _⇐;
        idl = idl;
        idr = idr
      } where
        ⇒ : A → (A ＋ B)
        ⇒ a = inj₁ a

        _⇐ : (A ＋ B) → Maybe A
        (inj₁ a) ⇐ = just a
        (inj₂ b) ⇐ = nothing

        idl : ∀ {a : A} → ⇒ a ⇐ ≡ just a
        idl = refl

        idr : ∀ {a : A} {ab : A ＋ B} →
              ab ⇐ ≡ just a →
              ⇒ a ≡ ab
        idr {a} {inj₁ a} refl = refl

    𝟘⊑𝟙 : 𝟘 ⊑ 𝟙
    𝟘⊑𝟙 = record {
      ⇒ = ⇒;
      _⇐ = _⇐;
      idl = idl;
      idr = λ ()
      } where
        ⇒ = λ ()
        _⇐ = λ tt → nothing

        idl : ∀ {𝟘x : 𝟘} → ⇒ 𝟘x ⇐ ≡ just 𝟘x
        idl {()}

  BaseModel : BaseTT BaseTys PI
  BaseModel = record {BaseModel}

