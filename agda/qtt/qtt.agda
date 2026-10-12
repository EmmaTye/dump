open import semiring

module qtt where

  record QTT-Sorts : Set₁ where
    field
      R : Set
      SemRing : Semiring R
      Con : Set
      Ty : Con → Set
      Tm : (Γ : Con) → Ty Γ → Set
      Sub : Con → Con → Set
      𝐕 : Set
  
  module QTT-Sig (qtt-sorts : QTT-Sorts) where
    open QTT-Sorts qtt-sorts
    variable
      ρ π ο : R
      Γ Δ Θ : Con
      A B C : Ty _
      t u v : Tm _ _
      σ δ ν : Sub _ _
    
    record QTT-Sig : Set where
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
  
 

  record QTT-Syntax (qtt-sorts : QTT-Sorts) : Set₁ where
    open QTT-Sorts qtt-sorts
    field
      -- Type construction
      _⇒_ : ∀ {Γ : Con} → Ty Γ → Ty Γ → Ty Γ
      𝕊𝕖𝕥 : ∀ {Γ : Con} → Ty Γ

      -- Term construction
      Type : ∀ {Γ : Con} (S : Ty Γ) → Tm Γ 𝕊𝕖𝕥
      -- TODO: add var to context
      Var : ∀ {Γ : Con} {A : Ty Γ} → 𝐕 → Tm Γ A

{-
  module QTT-Core (qtt-sorts : QTT-Sorts) where
    open QTT-Sorts qtt-sorts
    variable
      ρ π ο : R
      Γ Δ Θ : Con
      A B C : Ty _
      t u v : Tm _ _
      σ δ ν : Sub _ _
    
  module qtt-syntax (R : Set) 
                    (semiring : Semiring R) 
                    (𝐕 : Set) where
    
    variable
      ρ π ο : R
      x y z : 𝐕
    

    mutual
    
      data Assignment : Set where
        _∷_⦂_ : 𝐕 → R → Type → Assignment
      
      data Con : Set where
        ⋄ : Con
        _,_ : Con → Assignment → Con
        
      data Type : Set where
        _⇒_ : Assignment → Type → Type
        _⊗_ : Assignment → Type → Type
        𝕀 : Type
        𝔹 : Type
        El : Term → Type
    
      data Term : Set where
        Var : 𝐕 → Term
        Λ_∙_ : Assignment → Term → Term
        App⦂_∙_⦂_∙_ : Assignment → Type → Term → Term → Term
        ⟨_,_⟩⦂_∙_ : Term → Term → Assignment → Type → Term
        ⊤ : Term
-}

