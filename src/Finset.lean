
/-
So while writing this, I realized that to define finsets you
need Quotient types, which is why Mathlib defines finsets as
MultiSets.
-/

import Std.Data.List

import src.Util

/-
Map a function over a list, but do not include duplicates
-/
def List.mapNodup [BEq β] (f : α -> β) (l : List α) : List β :=
match l with
| [] => []
| h::t =>
  let ft : List β := List.mapNodup f t;
  let fh : β := f h;
  if List.elem fh ft then ft else fh::ft

/- List.mapNodup creates a list with no duplicates -/
theorem List.mapNodup_Nodup [BEq β] [LawfulBEq β] (f : α -> β) (l : List α) :
List.Nodup (List.mapNodup f l) := by
  induction l with
  | nil => simp [Nodup, List.mapNodup]
  | cons h t ih =>
    simp [Nodup, List.mapNodup]
    cases H : List.elem (f h) (mapNodup f t)
    case true =>
      simp
      exact ih
    case false =>
      simp
      apply And.intro
      case left =>
        intros a' H2 H3
        rw [←H3] at H2
        have H4 := elem_eq_true_of_mem H2
        rw [H4] at H
        simp at H
      case right =>
        exact ih

/-
A Finset is a set with a finite number of elements
It is represented as a list with a no duplicates constraint
-/
structure Finset (α : Type) where
  members : List α
  unique : members.Nodup

instance : Coe (Finset α) (List α) := ⟨Finset.members⟩
instance {H : x.Nodup} : CoeDep (List α) x (Finset α) := ⟨x, H⟩
instance : HasSubset (Finset α) := ⟨(·.members ⊆ ·.members)⟩
instance : Membership α (Finset α) := ⟨(· ∈ ·.members)⟩

def Finset.equals (f1 f2 : Finset α) : Prop := f1 ⊆ f2 ∧ f2 ⊆ f1

instance Finset.decEq_finset [DecidableEq α] (f1 f2 : Finset α) :
Decidable (Finset.equals f1 f2) := by
  have H : @DecidableRel (List α) (· ⊆ ·) := inferInstance
  have H1 : Decidable (f1 ⊆ f2) := H f1 f2
  have H2 : Decidable (f2 ⊆ f1) := H f2 f1
  have H3 : Decidable (f1 ⊆ f2 ∧ f2 ⊆ f1) := inferInstance
  assumption

instance [DecidableEq α] : BEq (Finset α) := ⟨λf1 f2 => decide (Finset.equals f1 f2)⟩

def Finset.map {α β : Type} [BEq β] [LawfulBEq β] (f : α -> β) (s : Finset α) : Finset β :=
  ⟨List.mapNodup f s, List.mapNodup_Nodup f s⟩

@[simp]
theorem Finset.self_subset (f : Finset α) : f ⊆ f := by
  intros _ H
  exact H

/-
A finite subset of a Finset F is a Finset with
A restriction that all all its members are in F
-/
structure Finsubset (F : Finset α) where
  subset : Finset α
  h : subset ⊆ F

--Dependent Coercion of a Finset x to a Finsubset
instance : CoeDep (Finset α) x (Finsubset x) := ⟨x, Finset.self_subset x⟩
instance : HasSubset (Finsubset α) := ⟨(·.subset ⊆ ·.subset)⟩

def Finsubset.Mem {F : Finset α} (s : Finsubset F) (a : α) : Prop :=
  a ∈ s.subset

instance {F : Finset α} : Membership α (Finsubset F) := ⟨(· ∈ ·.subset)⟩

theorem Finsubset.Mem_in_superset {F : Finset α} (S : Finsubset F) (x : α) :
x ∈ S → x ∈ F := by
  intro H
  exact S.h H
