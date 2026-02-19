
module cwf where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- TODO: is this a primitive anywhere? I can't see it
-- and if not, why not - is it discouraged? Why so?
coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
coe refl a = a

-- NOTE: we have a separate record for the sorts so that we can use implicit variables
-- in the equations for CwF
record CwF-sorts : Set1 where
  field
    Con : Set -- typing contexts (lists of types)
    Ty : Con → Set -- types in specific contexts, for dependent typing
    Tm : ∀ Γ → Ty Γ -> Set -- terms in a context, with a type in that context
    Sub : Con → Con -> Set -- parallel substitution, so Sub Γ Δ assigns a term in Γ to each variable from Δ
                            -- (list of terms, s.t. we have one list entry for each entry in Δ
module CwF-sig (s : CwF-sorts)  where
  open CwF-sorts s
  variable
    Γ Δ Θ : Con
    A B C : Ty _
    t u v : Tm _ _
    σ δ ν : Sub _ _

  record CwF-signature : Set where
    field
      -- Contexts
      · : Con -- empty context
      _,_ : (Γ : Con) →  Ty Γ -> Con -- extend a contex with a type (telescopically)
  
      -- Substitutions
      ϵ :  Sub Γ · -- empty substitution (list) - there are no variables in · so there are no assignments
                        -- (you can substitute the empty context into any context)
      _[_]ᵀ : Ty Δ → Sub Γ Δ → Ty Γ -- type substitution
      _,,_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ᵀ) → Sub Γ (Δ , A) -- substitution extension
      _∘_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ -- substituion composition

      _[_] : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ᵀ)

      id : Sub Γ Γ -- identity substitution
      p : Sub (Γ , A) Γ -- first projection/weakening rule (you can extend any context with an additional type)
      q : Tm (Γ , A) (A [ p ]ᵀ) -- second projection, gives the term at the start of a substitution
  
      -- Rules
      --- substitutions:
      ϵη : (σ : Sub Γ ·) → σ ≡ ϵ -- every empty subsitution must be ϵ
      [id] : A [ id ]ᵀ ≡ A -- ensuring that id does what we expect
      assSub : σ ∘ (δ ∘ ν) ≡ (σ ∘ δ) ∘ ν -- substitution is associative
      idl : id ∘ σ ≡ σ -- id preserves subsitutions on the left
      idr : σ ∘ id ≡ σ -- id preserves subsitutions on the left
      [∘]ᵀ : A [ σ ∘ δ ]ᵀ ≡ A [ σ ]ᵀ [ δ ]ᵀ -- composing substitutions composes their application 
                                           -- (ensures that composition does what we expect)
      p∘ : p ∘ (σ ,, t) ≡ σ -- projects first component of a substitution
      q[] : q [ σ ,, t ] ≡ coe (cong (Tm Γ) (trans (cong (A [_]ᵀ) (sym p∘)) [∘]ᵀ))
                           t
                          -- q projects the first component of a substitution out as a term

