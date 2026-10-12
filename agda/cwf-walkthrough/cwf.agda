open import Relation.Binary.PropositionalEquality
  hiding ([_])
open ≡-Reasoning

module cwf where

-- lemma
subst-sym : ∀ {A : Set} {P : A → Set} {a b : A}
              {b≡a : b ≡ a} {a≡b : a ≡ b} {x : P a} {y : P b} →
            x ≡ subst P b≡a y →
            subst P a≡b x ≡ y
subst-sym {b≡a = refl} {a≡b = refl} refl = refl

-- NOTE: we have a separate record for the sorts so that we can use implicit variables
-- in the equations for CwF
record CwF-sorts : Set1 where
  field
    Con : Set -- typing contexts (lists of types)
    Ty : Con → Set -- types in specific contexts, for dependent typing
    Tm : ∀ Γ → Ty Γ -> Set -- terms in a context, with a type in that context
    Sub : Con → Con -> Set -- parallel substitution, so Sub Γ Δ assigns a term in Γ to each variable from Δ

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
  
  record CwF-axioms (sig : CwF-signature) : Set where
    open CwF-signature sig
    field
      -- Rules
      --- substitutions:
      ϵη : (σ : Sub Γ ·) → σ ≡ ϵ -- every empty subsitution must be ϵ
      [id]ᵀ : A [ id ]ᵀ ≡ A -- ensuring that id does what we expect
      assSub : σ ∘ (δ ∘ ν) ≡ (σ ∘ δ) ∘ ν -- substitution is associative
      idl : id ∘ σ ≡ σ -- id preserves subsitutions on the left
      idr : σ ∘ id ≡ σ -- id preserves subsitutions on the left
      [∘]ᵀ : A [ σ ∘ δ ]ᵀ ≡ A [ σ ]ᵀ [ δ ]ᵀ -- composing substitutions composes their application 
                                           -- (ensures that composition does what we expect)
      p∘ : p ∘ (σ ,, t) ≡ σ -- projects first component of a substitution
      q[] : ∀ {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ]ᵀ)} → 
            q [ σ ,, t ] ≡ subst (Tm Γ) (begin
                                           (A [ σ ]ᵀ)
                                         ≡⟨ cong (A [_]ᵀ) (sym p∘) ⟩
                                           (A [ p ∘ (σ ,, t) ]ᵀ)
                                         ≡⟨ [∘]ᵀ ⟩
                                           ((A [ p ]ᵀ) [ σ ,, t ]ᵀ)
                                         ∎)
                                         t -- q projects the first component of a substitution out as a term
      ,η : (p {Γ} {A} ,, q) ≡ id
      ,∘ : ∀ {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ]ᵀ)} {δ : Sub Θ Γ} →
           (σ ,, t) ∘ δ ≡ (σ ∘ δ) ,, (subst (Tm Θ) (sym [∘]ᵀ) (t [ δ ]))


module CwF-proofs (s : CwF-sorts)
                  (sig : CwF-sig.CwF-signature s)
                  (axioms : CwF-sig.CwF-axioms s sig)
       where
  open CwF-sorts s
  open CwF-sig.CwF-signature sig
  open CwF-sig.CwF-axioms axioms
  variable
    Γ Δ Θ : Con
    A B C : Ty _
    t u v : Tm _ _
    σ δ ν : Sub _ _

  ση : ∀ {σ : Sub Γ (Δ , A)} →
       σ ≡ (p ∘ σ) ,, (subst (Tm Γ) (sym [∘]ᵀ) (q [ σ ]))
  ση {Γ = Γ} {σ = σ} =
    let
      q[σ] = (subst (Tm Γ) (sym [∘]ᵀ) (q [ σ ]))
    in
    begin
      σ
    ≡⟨ sym idl ⟩
      id ∘ σ
    ≡⟨ cong (_∘ σ) (sym ,η) ⟩
      (p ,, q) ∘ σ
    ≡⟨ ,∘ ⟩
      (p ∘ σ) ,, q[σ]
    ∎

  [id] : ∀ {A : Ty Γ} {t : Tm Γ A} → t [ id ] ≡ subst (Tm Γ) (sym [id]ᵀ) t
  [id] {Γ = Γ} {A = A} {t = t} =
    let
      t' = subst (Tm Γ) (sym [id]ᵀ) t
      q' = q [ (id ∘ id) ,, t[id]' ]
    in
    begin
      t [ id ]
    ≡⟨ {!!} ⟩ -- sym q[]
      subst (Tm Γ) A[p][σ,,t]≡A[σ]
        (q [ id ,, (t [ id ]) ])
    ≡⟨ {!!} ⟩ -- cong (q [ _,, (t [ id ])) (sym idl)
      subst (Tm Γ) A[p][σ∘id,,t]≡A[σ]
        (q [ (id ∘ id) ,, t[id]' ])
    ≡⟨ {!!} ⟩ -- cong (q [_]) (sym ,∘)
      subst (Tm Γ) A[p][σ,,t∘id]≡A[σ]
        (q [ (id ,, t') ∘ id ])
    ≡⟨ {!!} ⟩
      subst (Tm Γ) A[p][σ,,t]≡A[σ]
        (q [ id ,, t' ])
    ≡⟨ {!!} ⟩ -- q[]
      t'
    ∎
    where
      A[p][σ,,t]≡A[σ] : ∀ {Γ : Con} {A : Ty Γ} {σ : Sub Γ Γ} {t : Tm Γ (A [ σ ]ᵀ)} →
             (A [ p ]ᵀ) [ σ ,, t ]ᵀ ≡ A [ σ ]ᵀ
      A[p][σ,,t]≡A[σ] {A = A} {σ = σ} {t = t} =
        begin
          (A [ p ]ᵀ) [ σ ,, t ]ᵀ
        ≡⟨ sym [∘]ᵀ ⟩
          A [ p ∘ (σ ,, t) ]ᵀ
        ≡⟨ cong (A [_]ᵀ) p∘ ⟩
          A [ σ ]ᵀ
        ∎

      A[p][σ∘id,,t]≡A[σ] : ∀ {Γ : Con} {A : Ty Γ} {σ : Sub Γ Γ} {t : Tm Γ (A [ σ ∘ id ]ᵀ)} →
        (A [ p ]ᵀ) [ (σ ∘ id) ,, t ]ᵀ ≡ A [ σ ]ᵀ
      A[p][σ∘id,,t]≡A[σ] {Γ = Γ} {A = A} {σ = σ} {t = t} =
        begin
          (A [ p ]ᵀ) [ (σ ∘ id) ,, t ]ᵀ
        ≡⟨ cong ((A [ p ]ᵀ) [_]ᵀ) {!!} ⟩
          (A [ p ]ᵀ) [ σ ,, (subst (Tm Γ) (cong (A [_]ᵀ) idr) t) ]ᵀ
        ≡⟨ A[p][σ,,t]≡A[σ] ⟩
          A [ σ ]ᵀ
        ∎

      A[p][σ,,t∘id]≡A[σ] : ∀ {Γ : Con} {A : Ty Γ} {σ : Sub Γ Γ} {t : Tm Γ (A [ σ ]ᵀ)} →
        (A [ p ]ᵀ) [ (σ ,, t) ∘ id ]ᵀ ≡ A [ σ ]ᵀ
      A[p][σ,,t∘id]≡A[σ] {A = A} {σ = σ} {t = t} =
        begin
          (A [ p ]ᵀ) [ (σ ,, t) ∘ id ]ᵀ
        ≡⟨ cong ((A [ p ]ᵀ [_]ᵀ)) idr ⟩
          (A [ p ]ᵀ) [ (σ ,, t) ]ᵀ
        ≡⟨ A[p][σ,,t]≡A[σ] ⟩
          A [ σ ]ᵀ
        ∎

      t[id]' : Tm Γ (A [ id ∘ id ]ᵀ)
      t[id]' = subst (Tm Γ) (cong (A [_]ᵀ) (sym idl)) (t [ id ])

