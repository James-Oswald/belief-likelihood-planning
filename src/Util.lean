

theorem forall_neg (p : α->Prop) : (¬∀ a : α, p a) <-> (∃ a : α, ¬p a) := by
  apply Iff.intro
  . intro H
    apply Classical.byContradiction
    intro H2
    apply H
    intro a
    apply Classical.byContradiction
    intro H3
    apply H2
    apply Exists.intro a
    assumption
  . intro ⟨w, H⟩ H2
    have H3 := H2 w
    contradiction

theorem exists_neg (p : α->Prop) : (¬∃ a : α, p a) <-> (∀ a : α, ¬p a) := by
  apply Iff.intro
  . intros H a H2
    apply H
    apply Exists.intro a
    assumption
  . intros H H2
    have ⟨w, H3⟩ := H2
    have H4 := H w
    contradiction

theorem not_P_imp_not_Q_imp_P_and_Q (A B : Prop) : ¬(A -> ¬B) -> A ∧ B := by
  intro H
  apply Classical.byContradiction
  intro H2
  apply H
  intro H3 H4
  have H5 := And.intro H3 H4
  contradiction

theorem contrapositive {A B : Prop} : (A -> B) <-> (¬B -> ¬A) := by
  apply Iff.intro
  . intro H H2 H3
    have L1 := H H3
    contradiction
  . intro H H2
    apply Classical.byContradiction
    intro H3
    have L1 := H H3
    contradiction

theorem doubleNeg {A : Prop} : ¬¬A <-> A := by
  apply Iff.intro
  . intro H
    apply Classical.byContradiction
    intro H2
    contradiction
  . intro H H2
    contradiction

theorem List.elem_eq_false_of_not_mem [BEq α] [LawfulBEq α] {a : α} {as : List α} :
a ∉ as → elem a as = false := by
  rw [contrapositive, doubleNeg]
  simp
  exact List.mem_of_elem_eq_true
