/-
# Simply Typed Lambda Calculus with Products and Sums - Types

This module defines simple types extended with products and sums.

## Overview

Simple types now include:
- Base types (e.g., Bool, Nat)
- Function types (A → B)
- Product types (A × B)
- Sum types (A + B)

## References

- Pierce, "Types and Programming Languages" (2002), Chapters 11 and 12
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

namespace Metatheory.STLCext

-- TODO Document everything related to STLCspec
class STLCspec where
  baseTypes : Type _
  baseTypeValue : baseTypes → Type _
  [decEqBase : DecidableEq baseTypes]
  [reprBase : Repr baseTypes]
  [decEqValues : ∀ t : baseTypes, DecidableEq (baseTypeValue t)]
  [reprValues : ∀ t : baseTypes, Repr (baseTypeValue t)]

@[reducible]
def BaseTypes [inst : STLCspec] := inst.baseTypes
@[reducible]
def BaseTypeValue [inst : STLCspec] : BaseTypes → Type _ := inst.baseTypeValue

instance [s : STLCspec] : DecidableEq BaseTypes := s.decEqBase
instance [s : STLCspec] : Repr BaseTypes := s.reprBase
instance [s : STLCspec] (t: BaseTypes) : DecidableEq (BaseTypeValue t) := s.decEqValues t
instance [s : STLCspec] (t: BaseTypes) : Repr (BaseTypeValue t) := s.reprValues t

/-! ## Simple Types with Products and Sums -/

section Spec
variable [spec: STLCspec]

/-- Simple types: base types, function types, products, sums, and unit -/
inductive Ty where
  | base : BaseTypes → Ty        -- Base type indexed by natural number
  | arr  : Ty → Ty → Ty    -- Function type A → B
  | prod : Ty → Ty → Ty    -- Product type A × B
  | sum  : Ty → Ty → Ty    -- Sum type A + B
  | unit : Ty              -- Unit type (terminal object)
deriving DecidableEq, Repr

/-- Notation for function types -/
scoped infixr:70 " ⇒ " => Ty.arr

/-- Notation for product types -/
scoped infixl:75 " ⊗ " => Ty.prod

/-- Notation for sum types -/
scoped infixl:65 " ⊕ " => Ty.sum

namespace Ty

/-! ## Type Properties -/

/-- A type is ground (has no type constructors) -/
def isGround : Ty → Bool
  | base _ => true
  | arr _ _ => false
  | prod _ _ => false
  | sum _ _ => false
  | unit => true

/-- Size of a type (number of type constructors) -/
def size : Ty → Nat
  | base _ => 1
  | arr a b => 1 + size a + size b
  | prod a b => 1 + size a + size b
  | sum a b => 1 + size a + size b
  | unit => 1

/-- Depth of a type (maximum nesting) -/
def depth : Ty → Nat
  | base _ => 0
  | arr a b => 1 + max (depth a) (depth b)
  | prod a b => 1 + max (depth a) (depth b)
  | sum a b => 1 + max (depth a) (depth b)
  | unit => 0

/-! ## Type Examples -/

/-- Identity type: A → A -/
def idTy (A : Ty) : Ty := A ⇒ A

/-- Pair type: A × B -/
def pairTy (A B : Ty) : Ty := A ⊗ B

/-- Either type: A + B -/
def eitherTy (A B : Ty) : Ty := A ⊕ B

/-- Church boolean type: A → A → A -/
def churchBool (A : Ty) : Ty := A ⇒ A ⇒ A

/-- Church natural type: (A → A) → A → A -/
def churchNat (A : Ty) : Ty := (A ⇒ A) ⇒ A ⇒ A

end Ty

end Spec

/-! ## Common Base Types -/

namespace Ty
section BaseTypeExamples

local instance exampleSpec : STLCspec where
  baseTypes := Bool
  baseTypeValue t := if t then Bool else Nat
  decEqValues t := match t with | true => inferInstanceAs (DecidableEq Bool) | false => inferInstanceAs (DecidableEq Nat)
  reprValues t := match t with | true => inferInstanceAs (Repr Bool) | false => inferInstanceAs (Repr Nat)

/-- Base type Bool -/
abbrev TBool : Ty := base true

/-- Base type Nat -/
abbrev TNat : Ty := base false

/-- Unit type -/
abbrev TUnit : Ty := Ty.unit

end BaseTypeExamples

end Ty

end Metatheory.STLCext
