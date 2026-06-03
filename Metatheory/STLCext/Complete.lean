import Metatheory.STLCext.Parallel

/-!
# Complete Development for Extended STLC

This module defines complete development for STLC with products and sums.
It is used to prove the diamond property for parallel reduction.

## Key Lemma

If M ⇒ N, then N ⇒ complete M.

This yields diamond: N₁ ⇒ complete M and N₂ ⇒ complete M.

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Pierce, "Types and Programming Languages" (2002), Chapters 11-12
-/

namespace Metatheory.STLCext

section Spec
variable [STLCspec]

open Term

/-! ## Complete Development -/

/-- Complete development: reduce all redexes in a term. -/
noncomputable
def complete : Term → Term
  | var n => var n
  | lam M => lam (complete M)
  | app (lam M) N => (complete M)[complete N]
  | app (@func _ t u ht hu f) N =>
      let N' := complete N
      open Classical in
      if h : Term.isBasicType t N' then BasicTerm.toTerm (f (Term.toBasicTerm t N' h))
      else Term.app (@Term.func _ t u ht hu f) N'
  | app M N => app (complete M) (complete N)
  | pair M N => pair (complete M) (complete N)
  | fst (pair M _) => complete M
  | fst M => fst (complete M)
  | snd (pair _ N) => complete N
  | snd M => snd (complete M)
  | inl M => inl (complete M)
  | inr M => inr (complete M)
  | case (inl V) N₁ _ => (complete N₁)[complete V]
  | case (inr V) _ N₂ => (complete N₂)[complete V]
  | case M N₁ N₂ => case (complete M) (complete N₁) (complete N₂)
  | unit => unit
  | value v => value v
  | @func _ t u ht hu f => @func _ t u ht hu f

/-! ## Basic Properties -/

@[simp] theorem complete_var (n : Nat) : complete (var n) = var n := rfl
@[simp] theorem complete_lam (M : Term) : complete (lam M) = lam (complete M) := rfl
@[simp] theorem complete_beta (M N : Term) : complete (app (lam M) N) = (complete M)[complete N] := rfl
@[simp] theorem complete_fst_pair (M N : Term) : complete (fst (pair M N)) = complete M := rfl
@[simp] theorem complete_snd_pair (M N : Term) : complete (snd (pair M N)) = complete N := rfl
@[simp] theorem complete_case_inl (V N₁ N₂ : Term) :
    complete (case (inl V) N₁ N₂) = (complete N₁)[complete V] := rfl
@[simp] theorem complete_case_inr (V N₁ N₂ : Term) :
    complete (case (inr V) N₁ N₂) = (complete N₂)[complete V] := rfl

/-! ## Diamond Property via Complete Development -/

/-- Inversion for inl under parallel reduction. -/
theorem par_inl_inv {M M' : Term} (h : inl M ⇒ inl M') : M ⇒ M' := by
  cases h with
  | inl h' => exact h'

/-- Inversion for inr under parallel reduction. -/
theorem par_inr_inv {M M' : Term} (h : inr M ⇒ inr M') : M ⇒ M' := by
  cases h with
  | inr h' => exact h'

/-- Inversion for pairs under parallel reduction. -/
theorem par_pair_inv {M M' N N' : Term} (h : pair M N ⇒ pair M' N') : M ⇒ M' ∧ N ⇒ N' := by
  cases h with
  | pair hM hN => exact ⟨hM, hN⟩

theorem complete_isBasicType (hb : isBasicType t N) : complete N = N := by
  induction t generalizing N with
  | unit =>
    cases N with
    | unit => rfl
    | _ => simp_all [isBasicType]
  | base bt =>
    cases N with
    | value v => rfl
    | _ => simp_all [isBasicType]
  | arr A B ihA ihB =>
    cases N <;> simp_all [isBasicType]
  | prod a b iha ihb =>
    cases N with
    | pair N₁ N₂ =>
      simp only [isBasicType] at hb
      obtain ⟨hb₁, hb₂⟩ := hb
      simp [complete, iha hb₁, ihb hb₂]
    | _ => simp_all [isBasicType]
  | sum a b iha ihb =>
    cases N with
    | inl N' =>
      simp only [isBasicType] at hb
      simp [complete, iha hb]
    | inr N' =>
      simp only [isBasicType] at hb
      simp [complete, ihb hb]
    | _ => simp_all [isBasicType]

theorem par_isBasicType (h : M ⇒ N) (hb : isBasicType t M) : M = N := by
  induction t generalizing M N with
  | unit =>
    cases M with
    | unit => cases h; rfl
    | _ => simp_all [isBasicType]
  | base bt =>
    cases M with
    | value v => cases h; rfl
    | _ => simp_all [isBasicType]
  | arr A B ihA ihB =>
    cases M <;> simp_all [isBasicType]
  | prod a b iha ihb =>
    cases M with
    | pair M₁ M₂ =>
      simp only [isBasicType] at hb
      obtain ⟨hb₁, hb₂⟩ := hb
      cases h with
      | pair h₁ h₂ => rw [iha h₁ hb₁, ihb h₂ hb₂]
    | _ => simp_all [isBasicType]
  | sum a b iha ihb =>
    cases M with
    | inl M' =>
      simp only [isBasicType] at hb
      cases h with
      | inl h₁ => rw [iha h₁ hb]
    | inr M' =>
      simp only [isBasicType] at hb
      cases h with
      | inr h₂ => rw [ihb h₂ hb]
    | _ => simp_all [isBasicType]

theorem par_preserves_isBasicType (h : M ⇒ N) (h' : isBasicType t M) : isBasicType t N := by
    let eq : M = N := par_isBasicType h h'
    simp [← eq, h']

/-- If M ⇒ N, then N ⇒ complete M. -/
theorem par_complete {M N : Term} (h : M ⇒ N) : N ⇒ complete M := by
  induction h with
  | var n =>
    exact ParRed.refl _
  | lam hM ih =>
    exact ParRed.lam ih
  | @app M M' N N' hM hN ihM ihN =>
    cases hM with
    | var n =>
      simp [complete]
      exact ParRed.app ihM ihN
    | app _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | lam hBody =>
      simp [complete]
      exact ParRed.beta (by
        cases ihM with
        | lam ihBody => exact ihBody
        | _ => exact ParRed.refl _) ihN
    | beta _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | pair _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | fst _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | snd _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | inl _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | inr _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | case _ _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | fstPair _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | sndPair _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | caseInl _ _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | caseInr _ _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | unit =>
      simp [complete]
      exact ParRed.app ihM ihN
    | value v =>
      simp [complete]
      exact ParRed.app ihM ihN
    | @func t u ht hu f =>
      simp only [complete]
      split
      · exact ParRed.funcApp ihN ‹_›
      · exact ParRed.app (ParRed.func f) ihN
    | @funcApp t u ht hu f K K' K_red_K'' basic_K' =>
        let compl_fK := complete (Term.app (func (ht:=ht) (hu:=hu) f) K)
        let fK' := (f (toBasicTerm t K' basic_K')).toTerm
        have ihM : fK' ⇒ compl_fK := ihM
        have basic_fK' : isBasicType u fK' := isBasicType_toTerm _
        have eq : fK' = compl_fK := par_isBasicType ihM basic_fK'
        apply ParRed.app
        · change fK' ⇒ compl_fK
          simp [eq, ParRed.refl]
        · exact ihN
  | pair hM hN ihM ihN =>
    simp [complete]
    exact ParRed.pair ihM ihN
  | fst hM ih =>
    cases hM with
    | pair hM hN =>
      simp [complete]
      have hpair := par_pair_inv ih
      exact ParRed.fstPair hpair.1 hpair.2
    | _ =>
      simp [complete]
      exact ParRed.fst ih
  | snd hM ih =>
    cases hM with
    | pair hM hN =>
      simp [complete]
      have hpair := par_pair_inv ih
      exact ParRed.sndPair hpair.1 hpair.2
    | _ =>
      simp [complete]
      exact ParRed.snd ih
  | inl hM ih =>
    simp [complete]
    exact ParRed.inl ih
  | inr hM ih =>
    simp [complete]
    exact ParRed.inr ih
  | case hM hN₁ hN₂ ihM ihN₁ ihN₂ =>
    cases hM with
    | inl hV =>
      simp [complete]
      exact ParRed.caseInl (par_inl_inv ihM) ihN₁ ihN₂
    | inr hV =>
      simp [complete]
      exact ParRed.caseInr (par_inr_inv ihM) ihN₁ ihN₂
    | _ =>
      simp [complete]
      exact ParRed.case ihM ihN₁ ihN₂
  | beta hM hN ihM ihN =>
    simp [complete]
    exact ParRed.subst ihM ihN
  | fstPair hM hN ihM ihN =>
    simp [complete]
    exact ihM
  | sndPair hM hN ihM ihN =>
    simp [complete]
    exact ihN
  | caseInl hV hN₁ hN₂ ihV ihN₁ ihN₂ =>
    simp [complete]
    exact ParRed.subst ihN₁ ihV
  | caseInr hV hN₁ hN₂ ihV ihN₁ ihN₂ =>
    simp [complete]
    exact ParRed.subst ihN₂ ihV
  | unit =>
    simp [complete]
    exact ParRed.unit
  | value v =>
    simp [complete]
    exact ParRed.value v
  | func f =>
    simp [complete]
    exact ParRed.func f
  | @funcApp t u ht hu f N N' hN basic_N' ihN =>
    simp only [complete]
    split
    · rename_i basic_N
      -- let complete_stuck := complete_isBasicType basic_N'
      have N'_eq_completeN := par_isBasicType ihN basic_N'
      simp [N'_eq_completeN]
      apply ParRed.refl
    · grind only [par_isBasicType]

/-- Parallel reduction satisfies diamond. -/
theorem diamond {M N₁ N₂ : Term} (h1 : M ⇒ N₁) (h2 : M ⇒ N₂) :
    ∃ P, (N₁ ⇒ P) ∧ (N₂ ⇒ P) :=
  ⟨complete M, par_complete h1, par_complete h2⟩

end Spec
end Metatheory.STLCext
