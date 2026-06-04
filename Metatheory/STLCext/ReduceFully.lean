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
-- TODO move where appropriate
inductive IsDeepValue : Term → Prop where
  | var   : IsDeepValue (var n)
  | unit  : IsDeepValue unit
  | value : IsDeepValue (value v)
  | func  : IsDeepValue (@func _ t u ht hu f)
  | lam   : IsDeepValue M → IsDeepValue (lam M)
  | pair  : IsDeepValue M → IsDeepValue N → IsDeepValue (pair M N)
  | inl   : IsDeepValue M → IsDeepValue (inl M)
  | inr   : IsDeepValue M → IsDeepValue (inr M)
  | fst   : IsDeepValue M → (∀ A B, M ≠ pair A B) → IsDeepValue (fst M)
  | snd   : IsDeepValue M → (∀ A B, M ≠ pair A B) → IsDeepValue (snd M)
  | app : IsDeepValue M → IsDeepValue N →
            (∀ B, M ≠ lam B) →
            (∀ (t u : Ty) (ht : t.isArrowFree) (hu : u.isArrowFree)
               (f : BasicTerm t → BasicTerm u), Term.isBasicType t N → M ≠ @func _ t u ht hu f) →
            IsDeepValue (app M N)
  | case  : IsDeepValue M → IsDeepValue N₁ → IsDeepValue N₂ →
            (∀ V, M ≠ inl V) → (∀ V, M ≠ inr V) →
            IsDeepValue (case M N₁ N₂)

#check IsValue
-- TODO move where appropriate
theorem isDeepValue_iff_isNormalForm (M : Term) :
    IsDeepValue M ↔ IsNormalForm Step M := by
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

def reduction_step (term : Term) (ht : HasType ctxt term ty) (_: ¬ IsValue term) : Term := match term with
  | app (lam M) N =>
     have htN : HasType sorry N sorry := sorry
     if h : ¬ IsValue N then
       app (lam M) (reduction_step N htN h)
     else
       M[N]
  | app (@Term.func _ t u ht hu f) N =>
     have htN : HasType sorry N sorry := sorry
     if h : ¬ IsValue N then
       app (@Term.func _ t u ht hu f) (reduction_step N htN h)
     else if isBasicTerm' N then
       let h : isBasicType t N := sorry
       BasicTerm.toTerm (f (Term.toBasicTerm t N h))
     else
       False.elim sorry
  | app M N =>
     have htM : HasType sorry M sorry := sorry
     have htN : HasType sorry N sorry := sorry
     if h : ¬ IsValue M then
       app (reduction_step M htM h) N
     else
       have h : ¬ IsValue N := sorry
       app M (reduction_step N htN h)
  | fst (pair M N) => M -- shortcutting
  | snd (pair M N) => N -- shortcutting
  | case (inl V) N₁ N₂ => N₁[V] -- shortcutting
  | case (inr V) N₁ N₂ => N₂[V] -- shortcutting
  | lam M =>
     have htM : HasType sorry M sorry := sorry
     have h : ¬ IsValue M := sorry
     lam (reduction_step M htM h)
  | pair M N =>
     have htM : HasType sorry M sorry := sorry
     have htN : HasType sorry N sorry := sorry
     if h : ¬ IsValue M then
       pair (reduction_step M htM h) N
     else
       have h : ¬ IsValue N := sorry
       pair M (reduction_step N htN h)
  | fst M =>
     have htM : HasType sorry M sorry := sorry
     have h : ¬ IsValue M := sorry
     fst (reduction_step M htM h)
  | snd M =>
     have htM : HasType sorry M sorry := sorry
     have h : ¬ IsValue M := sorry
     snd (reduction_step M htM h)
  | inl M =>
     have htM : HasType sorry M sorry := sorry
     have h : ¬ IsValue M := sorry
     inl (reduction_step M htM h)
  | inr M =>
     have htM : HasType sorry M sorry := sorry
     have h : ¬ IsValue M := sorry
     inr (reduction_step M htM h)
  | case M N O =>
     have htM : HasType sorry M sorry := sorry
     have htN : HasType sorry N sorry := sorry
     have htO : HasType sorry O sorry := sorry
     if h : ¬ IsValue M then
       case (reduction_step M htM h) N O
     else if h : ¬ IsValue N then
       case M (reduction_step N htN h) O
     else
       have h : ¬ IsValue O := sorry
       case M N (reduction_step O htO h)
  | _ => False.elim sorry

theorem reduction_step_preservation (term : Term) (ht : HasType ctxt term ty) (red : ¬ IsValue term) :
    HasType ctxt (reduction_step term ht red) ty := sorry

theorem reduction_step_Step (term : Term) (ht : HasType ctxt term ty) (red : ¬ IsValue term) :
    term ⟶ (reduction_step term ht red) := sorry

def reduce_fully (term : Term) (ht : HasType ctxt term ty) : Term :=
    if h : IsValue term then
      term
    else
      let term' := reduction_step term ht h
      have ht' : HasType ctxt term' ty := reduction_step_preservation term ht h
      reduce_fully term' ht'
termination_by false -- TODO Put something suitable here
decreasing_by sorry

theorem reduce_fully_IsValue (term : Term) (ht : HasType ctxt term ty) :
    IsValue (reduce_fully term ht) := sorry

/-- `reduce_fully h` is reachable from `M` by multi-step reduction. -/
theorem reduce_fully_reduces {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    M ⟶* reduce_fully M h :=
    sorry

/-- `reduce_fully h` is a normal form: no further reduction steps apply. -/
theorem reduce_fully_isNormalForm {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    IsNormalForm Step (reduce_fully M h) := sorry

/-- Any normal form reachable from `M` equals `reduce_fully h`. -/
theorem reduce_fully_unique {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A)
    {N : Term} (hsteps : M ⟶* N) (hval : IsValue N) : N = reduce_fully M h :=
  sorry

/-- Any normal form reachable from `M` equals `reduce_fully h`. -/
theorem reduce_fully_unique' {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A)
    {N : Term} (hsteps : M ⟶* N) (hnf : IsNormalForm Step N) : N = reduce_fully M h :=
  sorry

end Spec

end Metatheory.STLCext
