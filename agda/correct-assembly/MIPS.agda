open import Data.Nat
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec
open import Data.Vec.Properties
open import Data.Maybe
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)

--------------------------------------------------------------
-- Intrinsically type- and jump-safe MIPS programs
--
-- TODOs:
-- - add stack and memory types
-- - add more possible values, such as char, unsigned int, etc
-- - separate registers into categories: tmp, saved, arg, ret, stack pointer, frame pointer, ret addr
-- - add other branching ops
-- - add arithmetic and bitwise ops
--------------------------------------------------------------
module MIPS where

-- Number of registers
rn = 30

--------------------------------------------------------------
-- The typing system takes inspiration from Morrisett et al.'s paper "Stack-based typed assembly language" (DOI 10.1017/S0956796801004178)
--
-- ρ ::= ValueType | addr Γ       (register types)
-- Γ ::= {r₁ : ρ₁, ..., rₙ : ρₙ}  (register contexts)
-- Λ ::= {ℓ₁ : Γ₁, ..., ℓₙ : Γₙ}  (unidirectional label contexts)
-- τ ::= Γ ▹ Λ , Λ' (program types)
--
-- The idea of typing labels and program addresses with their necessary register contexts comes from the paper above, but my own idea is having two separate label contexts - one for keeping track of what labels we've seen so far and the other for storing what labels need to come. This allows us to safely jump either backwards (into Λ) or forwards (into Λ').
-- Note that I'm using de Bruijn indices for the labels and registers.
--------------------------------------------------------------
module Types where

  data ValueType : Set where
    Int : ValueType

  mutual
    data RegType : Set where
      val : ValueType → RegType
      addr : RegCtx → RegType
  
    RegCtx = Vec (Maybe RegType) rn

  record LabelCtx : Set where
    inductive
    constructor _,_
    field
      {noSeen} : ℕ
      {noFuture} : ℕ
      seen : Vec RegCtx noSeen
      future : Vec RegCtx noFuture

  record ProgType : Set where
    inductive
    constructor _▹_
    field
      -- Register context required to execute program
      regCtx : RegCtx
      -- Label context required to execute program
      labelCtx : LabelCtx

  infix 4 _,_
  infix 2 _▹_

open Types

private
  variable
    n m : ℕ
    ρ ρ' : RegType
    mρ mρ' : Maybe RegType
    Γ Γ' Γ¹ Γ² : RegCtx
    Λ Λ' : Vec RegCtx _
    τ τ' : ProgType
    vt vt' : ValueType

data Val : ValueType → Set where
  int : ℕ → Val Int

module register where

  data Register' (Γ : RegCtx) (mρ : Maybe RegType) : Set where
    $r' : (i : Fin rn) → Γ [ i ]= mρ → Register' Γ mρ

  Register : (Γ : RegCtx) (ρ : RegType) → Set
  Register Γ ρ = Register' Γ (just ρ)

  $r_ : {Γ : RegCtx} → (i : Fin rn) → Register' Γ (lookup Γ i)
  $r_ {Γ} i = $r' i (lookup⇒[]= i Γ refl)

  infix 10 $r_

  -- empty register context
  empʳ : RegCtx
  empʳ = replicate rn nothing

  -- updates register r in register context Γ with type ρ
  _,′_≔_ : (Γ : RegCtx) → (r : Register' Γ mρ) →
            (ρ : RegType) → RegCtx
  Γ ,′ ($r' i _) ≔ ρ = Γ [ i ]≔ just ρ

  infixl 4 _,′_≔_

  -- weakening relation
  private
    data _≼′_ : Vec (Maybe RegType) n →
                Vec (Maybe RegType) n →
                Set where
      nil≼′ : [] ≼′ []
      cons≼′ : {Γ : Vec (Maybe RegType) n} →
              {Γ' : Vec (Maybe RegType) n} →
              (mρ : Maybe RegType) →
              Γ ≼′ Γ' → (mρ ∷ Γ) ≼′ (mρ ∷ Γ')
      weaken′ : {Γ : Vec (Maybe RegType) n} →
                {Γ' : Vec (Maybe RegType) n} →
                (ρ : RegType) →
                Γ ≼′ Γ' → (nothing ∷ Γ) ≼′ (just ρ ∷ Γ')

  _≼_ : RegCtx → RegCtx → Set
  Γ ≼ Γ' = Γ ≼′ Γ'

  refl≼ : ∀ {Γ} → Γ ≼ Γ
  refl≼ {Γ} = aux Γ
    where
      aux : (Γ : Vec (Maybe RegType) n) →
            Γ ≼′ Γ
      aux [] = nil≼′
      aux (mρ ∷ Γ) = cons≼′ mρ (aux Γ)

  emp≼Γ : ∀ {Γ} → empʳ ≼ Γ
  emp≼Γ {Γ} = aux Γ
    where
      aux : (Γ : Vec (Maybe RegType) n) → 
            (replicate n nothing) ≼′ Γ
      aux [] = nil≼′
      aux (just ρ ∷ Γ) = weaken′ ρ (aux Γ)
      aux (nothing ∷ Γ) = cons≼′ nothing (aux Γ)

  weaken : ∀ {Γ Γ'} {ρ} → 
           (i : Fin rn) → Γ [ i ]= nothing →
           Γ ≼ Γ' →
           Γ ≼ (Γ' ,′ $r i ≔ ρ)
  weaken {Γ} {Γ'} {ρ} = aux Γ Γ'
    where
      aux : (Γ : Vec (Maybe RegType) n) →
            (Γ' : Vec (Maybe RegType) n) →
            (i : Fin n) →
            Γ [ i ]= nothing →
            Γ ≼′ Γ' →
            Γ ≼′ (Γ' [ i ]≔ (just ρ))
      aux (nothing ∷ Γ) (mρ ∷ Γ') 0F _ 
          (cons≼′ _ rec) = 
        weaken′ ρ rec
      aux (nothing ∷ Γ) (mρ ∷ Γ') 0F _ 
          (weaken′ _ rec) = 
        weaken′ ρ rec
      aux (mρ ∷ Γ) (mρ ∷ Γ') (Fin.suc i) 
          (there isNothing) (cons≼′ mρ rec) = 
        cons≼′ mρ (aux Γ Γ' i isNothing rec)
      aux (nothing ∷ Γ) (just ρ ∷ Γ') (Fin.suc i) 
          (there isNothing) (weaken′ ρ rec) =
        weaken′ ρ (aux Γ Γ' i isNothing rec)

open register

data ProgLabel : (Λ : Vec RegCtx n) (Γ : RegCtx) → 
                 Set where
  here : ProgLabel (Γ ∷ Λ) Γ
  there : ProgLabel Λ Γ → ProgLabel (Γ' ∷ Λ) Γ

--------------------------------------------------------------
-- We specify typed MIPS programs in CPS style, with de Bruijn indices being used for labels instead of naming them.
--
-- An entire MIPS program should start with an empty register context, no seen labels and all future labels to be populated:
-- Program (empʳ ▹ [] , Λ')
--------------------------------------------------------------
data Program : (τ : ProgType) → Set where
  -- Noop
  -- A finished MIPS program can exist in any register context and with any number of seen lables, but there must be no future labels still to be populated
  ϵ : Program (Γ ▹ Λ , [])
  
  -- Label
  -- When a program is labelled, the needed register context is annotated. The outer program should have a weaker register context than the label. The continuation then runs in the register context of the label, and the head of the "future labels" is moved to the head of the "seen labels". We currently also annotate with the weakening proof, although this should be automated.
  ℓ[_,_]⦂_ : (Γ : RegCtx) → 
             Γ ≼ Γ' →
             Program (Γ ▹ Γ ∷ Λ , Λ') →
             Program (Γ' ▹ Λ , Γ ∷ Λ')

  -- LOADING
  -- Load immediate value into register
  li_,_⨟_ : (r : Register' Γ mρ) →
            Val vt →
            Program (Γ ,′ r ≔ (val vt) ▹ Λ , Λ') →
            Program (Γ ▹ Λ , Λ')

  -- JUMPING - I'm differentiating between jumping backwards and jumping forwards to allow for the correct indices. The current register context must be weaker than the register context of the label we're jumping to, and we're currently annotating that weakening proof. Since we're unconditionally jumping, the continuation doesn't have to run under the current register context, but we do annotate the start of the next program with the intended register context.
  -- Jump backwards to point in code
  jb[_]_⨟[_]_ : Γ¹ ≼ Γ →
                ProgLabel Λ Γ¹ →
                (Γ² : RegCtx) →
                Program (Γ² ▹ Λ , Λ') →
                Program (Γ ▹ Λ , Λ')
  -- Jump forwards to point in code
  jf[_]_⨟[_]_ : Γ¹ ≼ Γ →
                ProgLabel Λ' Γ¹ →
                (Γ² : RegCtx) →
                Program (Γ² ▹ Λ , Λ') →
                Program (Γ ▹ Λ , Λ') 
  -- Jump to (backwards) label if registers are equal
  bbeq[_]_,_,_⨟_ : Γ' ≼ Γ →
                   Register Γ (val vt) → Register Γ (val vt) →
                   ProgLabel Λ Γ' →
                   -- If the branch fails, we continue the program, so the continuation needs to run in the current register context
                   Program (Γ ▹ Λ , Λ') →
                   Program (Γ ▹ Λ , Λ')
  -- Jump to (forwards) label if registers are equal
  bfeq[_]_,_,_⨟_ : Γ' ≼ Γ →
                   Register Γ (val vt) → Register Γ (val vt) →
                   ProgLabel Λ' Γ' →
                   -- If the branch fails, we continue the program, so the continuation needs to run in the current register context
                   Program (Γ ▹ Λ , Λ') →
                   Program (Γ ▹ Λ , Λ')

example : Program (empʳ ▹ [] , _)
example =   li $r 0F , (int 1) ⨟
            -- Can infer the continuation context from the label
            jf[ refl≼ ] (there here) ⨟[ _ ]
          ℓ[ empʳ ,′ $r 0F ≔ val Int ,′ $r 1F ≔ val Int , 
             refl≼ ]⦂
            bfeq[ emp≼Γ ] $r 0F , $r 1F , (there here) ⨟
          ℓ[ empʳ ,′ $r 0F ≔ val Int , 
             weaken 1F (there here) refl≼  ]⦂ 
            li ($r 1F) , (int 1) ⨟
            jb[ refl≼ ] (there here) ⨟[ empʳ ]
          ℓ[ empʳ , emp≼Γ ]⦂ ϵ

