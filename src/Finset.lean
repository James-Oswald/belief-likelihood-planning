/-
This file contains the definition of a Finsubset
as well as some custom machinery and theorems for Finsets
-/

import Mathlib.Data.Finset.Basic

/-
It is not obvious at all but Finset.Sort is what
allows you to actually convert a Finset to a List
in a computable way, Finset.toList is a psyop.
Also has a Repr instance.
-/
import Mathlib.Data.Finset.Sort


theorem Finset.self_subset {F : Finset α} : F ⊆ F := by
  intro x
  exact id

/-
A finite subset of a Finset F is a Finset with
A restriction that all all its members are in F
-/
structure Finsubset (F : Finset α) where
  subset : Finset α
  h : subset ⊆ F

instance : CoeDep (Finset α) x (Finsubset x) := ⟨x, Finset.self_subset⟩

--BEq Instances
instance Finsubset.Beq [DecidableEq α] {x : Finset α} : BEq (Finsubset x) :=
  ⟨(·.subset == ·.subset)⟩
instance {F : Finset String} : BEq (Finsubset F) := by exact Finsubset.Beq

--Subset Instances
def Finsubset.Subset {F : Finset α} (S1 S2: Finsubset F) : Prop := S1.subset ⊆ S2.subset

instance : HasSubset (Finsubset α) := ⟨Finsubset.Subset⟩

instance [DecidableEq α] {F : Finset α} {a b : Finsubset F} :
Decidable (a ⊆ b) := by
  simp [Subset, Finsubset.Subset]
  infer_instance

--Other Set Opperation Instances
instance {F : Finset α} : Membership α (Finsubset F) := ⟨(· ∈ ·.subset)⟩

instance [DecidableEq α] {F : Finset α} : SDiff (Finsubset F) where
  sdiff a b := ⟨a.subset \ b.subset, by
    intros x H
    exact a.h (Finset.sdiff_subset _ _ H)
  ⟩

instance [DecidableEq α] {F : Finset α} : Union (Finsubset F) where
  union a b := ⟨a.subset ∪ b.subset, Finset.union_subset a.h b.h⟩

@[simp]
theorem Finsubset.Mem_in_superset {F : Finset α} (S : Finsubset F) (x : α) :
x ∈ S → x ∈ F := by
  intro H
  exact S.h H
