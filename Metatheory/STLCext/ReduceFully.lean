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
