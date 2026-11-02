{-# OPTIONS #-}

open import Data.Bool as Bool
  using (Bool; true; false; not; if_then_else_; T)
open import Data.Empty
  using (⊥)
open import Data.Fin as Fin
  using (Fin)
open import Data.List
  as List
  using (List; _∷_; length; lookup)
open import Data.Maybe
  as Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  as ℕ
  using (ℕ; suc; zero; _*_; _+_)
open import Data.Nat.Properties
  as ℕ
  using ()
open import Data.Parity
  as Parity
  using (Parity; 0ℙ; 1ℙ)
open import Data.Product
  as Product
  using (_,_; _×_; Σ-syntax)
open import Data.Unit
  using (⊤; tt)
open import Data.Vec
  as Vec
  using (Vec)
open import Data.Vec.Properties
  as Vec
  using ()
open import Function.Base
  using (case_of_; _∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
  using (⌊_⌋)

module interpreter where

data Flag : Set where
  CF {- Carry flag -} : Flag
  ZF {- Zero flag -} : Flag
  OF {- Overflow flag -} : Flag
  HF {- Halt flag -} : Flag

module Word where
  -- Little-endian 32-bit words
  Word = Vec Bool 32
  
  _≟_ : Word → Word → Bool
  w ≟ w' = ⌊ Vec.≡-dec Bool._≟_ w w' ⌋

--  toℕ : Word → ℕ
--  toℕ = toℕ'
--    where
--    toℕ' : ∀ {n : ℕ} → Vec Bool n → ℕ
--    toℕ' Vec.[] = zero
--    toℕ' (false Vec.∷ v) = 2 * (toℕ' v)
--    toℕ' (true Vec.∷ v) = suc (2 * (toℕ' v))
--
--  parityToBool : Parity → Bool
--  parityToBool 0ℙ = false
--  parityToBool 1ℙ = true
--
--  {-# TERMINATING #-}
--  fromℕ : ℕ → Word × {- Overflow? -} Bool
--  fromℕ x = let w , n = fromℕ' x
--            in {!!}
--    where
--    fromℕ' : ℕ → Σ[ n ∈ ℕ ] Vec Bool n
--    fromℕ' zero = 0 , Vec.[]
--    fromℕ' (suc x) = let p = ℕ.parity (suc x)
--                         x' = ℕ.⌊ (suc x) /2⌋
--                         n , w = fromℕ' x'
--                     in suc n , (parityToBool p) Vec.∷ w

  isZero : Word → Bool
--  isZero w = Vec.foldr′  true w

  inc : Word → Word × {- Overflow? -} Bool
  inc w = inc' w
    where
    inc' : ∀ {n : ℕ} → Vec Bool n → Vec Bool n × Bool
    inc' Vec.[] = Vec.[] , true {- if we reach an empty vector, i.e. all the elements of w are true, then we've overflowed -}
    inc' (false Vec.∷ xs) = true Vec.∷ xs , false
    inc' (true Vec.∷ xs) = let xs' , of = inc' xs
                           in false Vec.∷ xs' , of

open Word

-- Infinite register pool
Reg = ℕ
RegState = Reg → Word
FlagState = Flag → Bool

Location = Word
Heap = Location → Maybe Word

record State : Set where
  field
    IP {- Instruction Pointer -} : ℕ
    rState : RegState
    fState : FlagState
    heap : Heap
open State

--------------------------------------------
-- State helpers

setIP : ℕ → State → State
setIP i s = record s { IP = i }

incIP : State → State
incIP s = record s { IP = suc (s .IP) }

setCF : Bool → State → State
setCF cf s = record s { fState = fState' }
  where
  fState' : FlagState
  fState' CF = cf
  fState' ZF = s .fState ZF
  fState' OF = s .fState OF
  fState' HF = s .fState HF

setZF : Bool → State → State
setZF zf s = record s { fState = fState' }
  where
  fState' : FlagState
  fState' CF = s .fState CF
  fState' ZF = zf
  fState' OF = s .fState OF
  fState' HF = s .fState HF

setOF : Bool → State → State
setOF of s = record s { fState = fState' }
  where
  fState' : FlagState
  fState' CF = s .fState CF
  fState' ZF = s .fState ZF
  fState' OF = of
  fState' HF = s .fState HF

setHF : Bool → State → State
setHF hf s = record s { fState = fState' }
  where
  fState' : FlagState
  fState' CF = s .fState CF
  fState' ZF = s .fState ZF
  fState' OF = s .fState OF
  fState' HF = hf

setReg : Reg → Word → State → State
setReg r w s = record s { rState = rState' }
  where
  rState' : RegState
  rState' r' = 
    if r' ℕ.≡ᵇ r
    then w
    else s .rState r'

storeLoc : Location → Word → State → State
storeLoc l w s = record s { heap = heap' }
  where
  heap' : Heap
  heap' l' = 
    if l ≟ l'
    then just w
    else s .heap l'

--------------------------------------------

data Instr : Set where
  {- Control flow instructions -}
  HLT {- Halt -} : Instr
  JMP {- Jump -} : ℕ → Instr
  JZE {- Jump if zero -} : ℕ → Instr
  JNE {- Jump if not zero -} : ℕ → Instr
  {- Loading/storing -}
  LDA {- Load into reg -} : Reg → Location → Instr
  STA {- Store reg -} : Reg → Location → Instr
  {- Unary op instructions -}
  INC {- Increment reg -} : Reg → (dst : Reg) → Instr
  DEC {- Decrement reg -} : Reg → (dst : Reg) → Instr
  NOT {- Flip all bits -} : Reg → (dst : Reg) → Instr
  NEG {- Integer negation -} : Reg → (dst : Reg) → Instr
  {- Binary op instructions -}
  ADC {- Add 2 regs with carry flag -} : Reg → Reg → (dst : Reg) → Instr
  SUB {- Subtract 2 regs -} : Reg → Reg → (dst : Reg) → Instr
  CMP {- Compare 2 regs, store 0 in ZF if equal -} : Reg → Reg → Instr
  AND {- And 2 regs -} : Reg → Reg → (dst : Reg) → Instr
  OR {- Or 2 regs -} : Reg → Reg → (dst : Reg) → Instr
  XOR {- Exclusive or -} : Reg → Reg → (dst : Reg) → Instr

-- Operational semantics
-- TODO:
{-# TERMINATING #-}
_,_⇓_ : List Instr → State → State → Set
is , s ⇓ s' = if s .fState HF
              then s ≡ s'
              else checkIP
  where
  evalInstr : Instr → Set
  {- HLT sets the halt flag -}
  evalInstr HLT = is , setHF true s ⇓ s'
  {- JMP sets the instruction pointer -}
  evalInstr (JMP i) = is , setIP i s ⇓ s'
  {- JZE sets the instruction pointer if the zero-flag is set -}
  evalInstr (JZE i) =
    if s .fState ZF
    then is , setIP i s ⇓ s'
    else is , incIP s ⇓ s'
  {- JNE sets the instruction pointer if the zero-flag isn't set -}
  evalInstr (JNE i) =
    if not (s .fState ZF)
    then is , setIP i s ⇓ s'
    else is , incIP s ⇓ s'
  {- LDA loads the word stored at location l into register r if it exists, otherwise undefined -}
  evalInstr (LDA r l) = case s .heap l of λ
    { (just w) → is , (incIP ∘ setReg r w) s ⇓ s'
    ; nothing → ⊥ 
    }
  {- STA stores the word in register r at location l in the heap -}
  evalInstr (STA r l) =
    let w = s .rState r in
    is , (incIP ∘ storeLoc l w) s ⇓ s'
  {- INCrements a register's value and stores it in the dst register, noting if it overflowed -}
  evalInstr (INC r dst) = 
    let w = s .rState r
        w' , of = inc w
        zf = isZero w'
    in is , (incIP ∘ setZF zf ∘ setOF of ∘ setReg dst w') s ⇓ s'
  evalInstr (DEC r dst) = {! !}
  evalInstr (NOT r dst) = {! !}
  evalInstr (NEG r dst) = {! !}
  evalInstr (ADC r r' dst) = {! !}
  evalInstr (SUB r r' dst) = {! !}
  evalInstr (CMP r r') = {! !}
  evalInstr (AND r r' dst) = {! !}
  evalInstr (OR r r' dst) = {! !}
  evalInstr (XOR r r' dst) = {! !}

  {- Check that the instruction pointer points to a valid instruction, and if so evaluate it -}
  checkIP : Set
  checkIP with  i ← s .IP
                | i ℕ.<ᵇ length is in eq
  checkIP | false = ⊥
  checkIP | true = 
    evalInstr (lookup is
               (Fin.fromℕ<
                {- Proof that i < length is -}
                (ℕ.<ᵇ⇒< i (length is)
                 {- TODO: not sure why rewrite isn't working and i'm having to do an explicit subst here -}
                 (subst T (sym eq) tt))))

