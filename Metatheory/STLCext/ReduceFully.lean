import Metatheory.STLCext.Normalization
import Metatheory.STLCext.Confluence

/-!
# Normal Form Function for Extended STLC

Every well-typed term of the extended STLC reduces to a unique normal form.
This combines:
- **Strong normalization** (Normalization.lean): every reduction sequence terminates.
- **Confluence** (Confluence.lean, via Complete.lean): any two reducts have a common reduct.

Together these give existence and uniqueness of normal forms, which we package
as a function `reduce_fully : HasType Γ M A → Term`.
-/

namespace Metatheory.STLCext

section Spec
variable [STLCspec]

open Term
open Rewriting (IsNormalForm Star)

/-- A term is in deep normal form: fully reduced including under binders. -/
inductive IsNormalForm' : Term → Prop where
  | var   : IsNormalForm' (var n)
  | unit  : IsNormalForm' unit
  | value : IsNormalForm' (value v)
  | func  : IsNormalForm' (@func _ t u ht hu f)
  | lam   : IsNormalForm' M → IsNormalForm' (lam M)
  | pair  : IsNormalForm' M → IsNormalForm' N → IsNormalForm' (pair M N)
  | inl   : IsNormalForm' M → IsNormalForm' (inl M)
  | inr   : IsNormalForm' M → IsNormalForm' (inr M)
  | fst   : IsNormalForm' M → (∀ A B, M ≠ pair A B) → IsNormalForm' (fst M)
  | snd   : IsNormalForm' M → (∀ A B, M ≠ pair A B) → IsNormalForm' (snd M)
  | app   : IsNormalForm' M → IsNormalForm' N →
            (∀ B, M ≠ lam B) →
            (∀ (t u : Ty) (ht : t.isArrowFree) (hu : u.isArrowFree)
               (f : BasicTerm t → BasicTerm u), Term.isBasicType t N → M ≠ @func _ t u ht hu f) →
            IsNormalForm' (app M N)
  | case  : IsNormalForm' M → IsNormalForm' N₁ → IsNormalForm' N₂ →
            (∀ V, M ≠ inl V) → (∀ V, M ≠ inr V) →
            IsNormalForm' (case M N₁ N₂)

theorem isNormalForm'_iff_isNormalForm (M : Term) :
    IsNormalForm' M ↔ IsNormalForm Step M := by
  constructor
  · intro h
    induction h with
    | var   => intro _ hN; exact nomatch hN
    | unit  => intro _ hN; exact nomatch hN
    | value => intro _ hN; exact nomatch hN
    | func  => intro _ hN; exact nomatch hN
    | lam _ ih =>
      intro _ hN; cases hN with | lam hstep => exact ih _ hstep
    | pair _ _ ihM ihN =>
      intro _ hN; cases hN with
      | pairL hstep => exact ihM _ hstep
      | pairR hstep => exact ihN _ hstep
    | inl _ ih =>
      intro _ hN; cases hN with | inl hstep => exact ih _ hstep
    | inr _ ih =>
      intro _ hN; cases hN with | inr hstep => exact ih _ hstep
    | fst _ hnotpair ih =>
      intro _ hN; cases hN with
      | fstPair     => exact hnotpair _ _ rfl
      | fst hstep   => exact ih _ hstep
    | snd _ hnotpair ih =>
      intro _ hN; cases hN with
      | sndPair     => exact hnotpair _ _ rfl
      | snd hstep   => exact ih _ hstep
    | app _ _ hnolam hnofunc ihM ihN =>
      intro _ hN; cases hN with
      | beta         => exact hnolam _ rfl
      | appL hstep   => exact ihM _ hstep
      | appR hstep   => exact ihN _ hstep
      | funcApp _ _ hb => exact hnofunc _ _ _ _ _ hb rfl
    | case _ _ _ hnoinl hnoinr ihM ihN₁ ihN₂ =>
      intro _ hN; cases hN with
      | caseInl      => exact hnoinl _ rfl
      | caseInr      => exact hnoinr _ rfl
      | caseS hstep  => exact ihM _ hstep
      | caseL hstep  => exact ihN₁ _ hstep
      | caseR hstep  => exact ihN₂ _ hstep

  · intro h
    induction M with
    | var   => exact .var
    | unit  => exact .unit
    | value => exact .value
    | func  => exact .func
    | lam M' ih =>
      exact .lam (ih fun P hP => h _ (Step.lam hP))
    | pair M' N' ihM ihN =>
      exact .pair (ihM fun P hP => h _ (Step.pairL hP))
                  (ihN fun P hP => h _ (Step.pairR hP))
    | inl M' ih =>
      exact .inl (ih fun P hP => h _ (Step.inl hP))
    | inr M' ih =>
      exact .inr (ih fun P hP => h _ (Step.inr hP))
    | fst M' ih =>
      exact .fst (ih fun P hP => h _ (Step.fst hP))
                 fun A B heq => by subst heq; exact h _ (Step.fstPair A B)
    | snd M' ih =>
      exact .snd (ih fun P hP => h _ (Step.snd hP))
                 fun A B heq => by subst heq; exact h _ (Step.sndPair A B)
    | app M' N' ihM ihN =>
      exact .app (ihM fun P hP => h _ (Step.appL hP))
                 (ihN fun P hP => h _ (Step.appR hP))
                 (fun B heq => by subst heq; exact h _ (Step.beta B N'))
                 (fun t u ht hu f hb heq => by subst heq; exact h _ (Step.funcApp f N' hb))
    | case M' N₁ N₂ ihM ihN₁ ihN₂ =>
      exact .case (ihM fun P hP => h _ (Step.caseS hP))
                  (ihN₁ fun P hP => h _ (Step.caseL hP))
                  (ihN₂ fun P hP => h _ (Step.caseR hP))
                  (fun V heq => by subst heq; exact h _ (Step.caseInl V N₁ N₂))
                  (fun V heq => by subst heq; exact h _ (Step.caseInr V N₁ N₂))

theorem isNormalForm'_implies_isValue {M : Term} {A : Ty}
    (ht : HasType [] M A) (hn : IsNormalForm' M) : IsValue M := by
  induction M generalizing A with
  | var _ => cases ht with | var h => simp at h
  | unit => exact trivial
  | value => exact trivial
  | func => exact trivial
  | lam _ _ => exact trivial
  | pair M N ihM ihN =>
    cases hn with
    | pair hnM hnN =>
      cases ht with
      | pair htM htN => exact ⟨ihM htM hnM, ihN htN hnN⟩
  | inl M ih =>
    cases hn with
    | inl hnM =>
      cases ht with
      | inl htM => exact ih htM hnM
  | inr M ih =>
    cases hn with
    | inr hnN =>
      cases ht with
      | inr htN => exact ih htN hnN
  | fst M ih =>
    cases hn with
    | fst hnM hnotpair =>
      cases ht with
      | fst htM =>
        have hvalM := ih htM hnM
        obtain ⟨M₁, M₂, heq⟩ := canonical_forms_prod htM hvalM
        exact absurd heq (hnotpair M₁ M₂)
  | snd M ih =>
    cases hn with
    | snd hnM hnotpair =>
      cases ht with
      | snd htM =>
        have hvalM := ih htM hnM
        obtain ⟨M₁, M₂, heq⟩ := canonical_forms_prod htM hvalM
        exact absurd heq (hnotpair M₁ M₂)
  | app M N ihM ihN =>
    cases hn with
    | app hnM hnN hnolam hnofunc =>
      cases ht with
      | app htM htN =>
        have hvalM := ihM htM hnM
        have hvalN := ihN htN hnN
        rcases canonical_forms_arr htM hvalM with ⟨M', rfl⟩ | ⟨t, u, haf, hu, f, rfl⟩
        · exact absurd rfl (hnolam M')
        · have hbasic : Term.isBasicType t N := by
            have htN' : HasType [] N t := by have hf := htM; cases hf; exact htN
            exact value_arrowFree_isBasicType htN' hvalN haf
          exact absurd rfl (hnofunc t u haf hu f hbasic)
  | case M N₁ N₂ ihM _ _ =>
    cases hn with
    | case hnM _ _ hnoinl hnoinr =>
      cases ht with
      | case htM _ _ =>
        have hvalM := ihM htM hnM
        rcases canonical_forms_sum htM hvalM with ⟨V, rfl⟩ | ⟨V, rfl⟩
        · exact absurd rfl (hnoinl V)
        · exact absurd rfl (hnoinr V)

def HasAnyType M := ∃ Γ A, HasType Γ M A

def reduction_step (term : Term) (ht : HasAnyType term) (_: ¬ IsValue term) : Term := match term with
  | app (lam M) N =>
     have htN : HasAnyType N := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | app _ htN => exact ⟨_, _, htN⟩
     if h : ¬ IsValue N then
       app (lam M) (reduction_step N htN h)
     else
       M[N]
  | app (@Term.func _ t u haf hu f) N =>
     have htN : HasAnyType N := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | app _ htN => exact ⟨_, _, htN⟩
     if h : ¬ IsValue N then
       app (@Term.func _ t u haf hu f) (reduction_step N htN h)
     else
       have hval_N : IsValue N := Classical.not_not.mp h
       have hbasic : isBasicType t N := by
         obtain ⟨Γ, A, ht'⟩ := ht
         cases ht' with | app htFunc htN =>
         cases htFunc with | func => exact value_arrowFree_isBasicType htN hval_N haf
       BasicTerm.toTerm (f (Term.toBasicTerm t N hbasic))
  | app M N =>
     have htM : HasAnyType M := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | app htM _ => exact ⟨_, _, htM⟩
     have htN : HasAnyType N := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | app _ htN => exact ⟨_, _, htN⟩
     if h : ¬ IsValue M then
       app (reduction_step M htM h) N
     else
       have h : ¬ IsValue N := sorry
       app M (reduction_step N htN h)
  | fst (pair M N) => M -- shortcutting
  | snd (pair M N) => N -- shortcutting
  | case (inl V) N₁ N₂ => N₁[V] -- shortcutting
  | case (inr V) N₁ N₂ => N₂[V] -- shortcutting
  | lam M => False.elim (by simp [IsValue] at *)
  | pair M N =>
     have htM : HasAnyType M := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | pair htM _ => exact ⟨_, _, htM⟩
     have htN : HasAnyType N := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | pair _ htN => exact ⟨_, _, htN⟩
     if h : ¬ IsValue M then
       pair (reduction_step M htM h) N
     else
       have h' : ¬ IsValue N := fun hN => ‹¬ IsValue (pair M N)› ⟨Classical.not_not.mp h, hN⟩
       pair M (reduction_step N htN h')
  | fst M =>
     have htM : HasAnyType M := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | fst htM => exact ⟨_, _, htM⟩
     have h : ¬ IsValue M := sorry
     fst (reduction_step M htM h)
  | snd M =>
     have htM : HasAnyType M := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | snd htM => exact ⟨_, _, htM⟩
     have h : ¬ IsValue M := sorry
     snd (reduction_step M htM h)
  | inl M =>
     have htM : HasAnyType M := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | inl htM => exact ⟨_, _, htM⟩
     inl (reduction_step M htM ‹¬ IsValue (inl M)›)
  | inr M =>
     have htM : HasAnyType M := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | inr htM => exact ⟨_, _, htM⟩
     inr (reduction_step M htM ‹¬ IsValue (inr M)›)
  | case M N O =>
     have htM : HasAnyType M := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | case htM _ _ => exact ⟨_, _, htM⟩
     have htN : HasAnyType N := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | case _ htN _ => exact ⟨_, _, htN⟩
     have htO : HasAnyType O := by obtain ⟨Γ, A, ht'⟩ := ht; cases ht' with | case _ _ htO => exact ⟨_, _, htO⟩
     if h : ¬ IsValue M then
       case (reduction_step M htM h) N O
     else if h : ¬ IsValue N then
       case M (reduction_step N htN h) O
     else
       have h : ¬ IsValue O := sorry
       case M N (reduction_step O htO h)
  | _ => False.elim sorry


theorem reduction_step_preservation (term : Term) (ht : HasType Γ term A) (red : ¬ IsValue term) :
    HasType Γ (reduction_step term ⟨_, _, ht⟩ red) A := sorry

theorem reduction_step_Step (term : Term) (ht : HasAnyType term) (red : ¬ IsValue term) :
    term ⟶ (reduction_step term ht red) := sorry

def reduce_fully (term : Term) (ht : HasAnyType term) : Term :=
    if h : IsValue term then
      term
    else
      let term' := reduction_step term ht h
      have ht' : HasAnyType term' := by
        rcases ht with ⟨Γ, A, ht⟩
        have ht' := reduction_step_preservation term ht h
        exact ⟨Γ, A, ht'⟩
      -- have ht' : HasType ctxt term' ty := reduction_step_preservation term ht h
      reduce_fully term' ht'
termination_by false -- TODO Put something suitable here
decreasing_by sorry

theorem reduce_fully_IsValue (term : Term) (ht : HasAnyType term) :
    IsValue (reduce_fully term ht) := sorry

/-- `reduce_fully h` is reachable from `M` by multi-step reduction. -/
theorem reduce_fully_reduces {Γ : Context} {M : Term} {A : Ty} (h : HasAnyType M) :
    M ⟶* reduce_fully M h :=
    sorry

/-- `reduce_fully h` is a normal form: no further reduction steps apply. -/
theorem reduce_fully_isNormalForm {M : Term} (h : HasAnyType M) :
    IsNormalForm Step (reduce_fully M h) := sorry

/-- Any normal form reachable from `M` equals `reduce_fully h`. -/
theorem reduce_fully_unique {M : Term} (h : HasAnyType M)
    {N : Term} (hsteps : M ⟶* N) (hval : IsNormalForm' N) : N = reduce_fully M h :=
  sorry

/-- Any normal form reachable from `M` equals `reduce_fully h`. -/
theorem reduce_fully_unique' {M : Term} (h : HasAnyType M)
    {N : Term} (hsteps : M ⟶* N) (hnf : IsNormalForm Step N) : N = reduce_fully M h :=
  sorry

end Spec

end Metatheory.STLCext
