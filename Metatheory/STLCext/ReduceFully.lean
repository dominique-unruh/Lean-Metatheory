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

/-! ## The reduce_fully Function -/

/-- Every well-typed term has a unique normal form. -/
private theorem unique_normalForm {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    ∃ N, Star Step M N ∧ IsNormalForm Step N ∧
      ∀ N', Star Step M N' ∧ IsNormalForm Step N' → N' = N :=
  Rewriting.existsUnique_normalForm_of_confluent_hasNormalForm
    step_confluent (hasNormalForm_of_hasType h)

/-- The unique normal form of a well-typed term. -/
noncomputable def reduce_fully {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) : Term :=
  Classical.choose (unique_normalForm h)

private theorem reduce_fully_spec {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    Star Step M (reduce_fully h) ∧ IsNormalForm Step (reduce_fully h) ∧
    ∀ N, Star Step M N ∧ IsNormalForm Step N → N = reduce_fully h :=
  Classical.choose_spec (unique_normalForm h)

/-- `reduce_fully h` is reachable from `M` by multi-step reduction. -/
theorem reduce_fully_reduces {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    M ⟶* reduce_fully h :=
  star_to_multiStep (reduce_fully_spec h).1

/-- `reduce_fully h` is a normal form: no further reduction steps apply. -/
theorem reduce_fully_isNormalForm {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    IsNormalForm Step (reduce_fully h) :=
  (reduce_fully_spec h).2.1

/-- Any normal form reachable from `M` equals `reduce_fully h`. -/
theorem reduce_fully_unique {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A)
    {N : Term} (hsteps : M ⟶* N) (hnf : IsNormalForm Step N) : N = reduce_fully h :=
  (reduce_fully_spec h).2.2 N ⟨multiStep_to_star hsteps, hnf⟩

end Spec
end Metatheory.STLCext
