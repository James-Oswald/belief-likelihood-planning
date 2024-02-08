
import src.Finset
import Mathlib.Data.List.Lex

#check String.decLt

structure Action (F : Finset String) where
  Name : String
  Pre : Finsubset F
  Add : Finsubset F
  Del : Finsubset F
deriving BEq

--We need a transitive, asymmetric, and decidable ordering on actions to
--Convert a Finset of actions to a list of actions via Finset.sort
def Action.lt (a b : Action F) : Prop :=
  a.Name.length ≤ b.Name.length

instance Action.instLT : LT (Action F) := ⟨Action.lt⟩

instance Action.instDecidableLT : Decidable (Action.lt a b) := by
  simp [Action.lt]
  apply inferInstance

instance Action.instIsTrans {F : Finset String} :
IsTrans (Action F) (@Action.lt F) := by
  apply IsTrans.mk
  intro a b c h₁ h₂
  simp [Action.lt] at *
  exact Nat.le_trans h₁ h₂

instance Action.instIsAntisymm {F : Finset String} :
IsAntisymm (Action F) (@Action.lt F) := by
  apply IsAntisymm.mk
  intro a b h₁ h₂
  simp [Action.lt] at *
  apply Nat.le_antisymm


/- A Classical Planning Problem -/
structure PlanProblem where
  F : Finset String         -- the set of facts
  A : Finset (Action F)     -- the set of actions
  S₀ : Finsubset F          -- the initial state
  G : Finset (Finsubset F)

/-
The type of states in a planning problem
-/
def State (π : PlanProblem) : Type := Finsubset π.F

/-
The type of plans that solve a planning problem
-/
structure Plan (π : PlanProblem) where
  --The list of actions that get to the goal state
  l : List (Action π.F)
  --A proof that all the actions are valid
  h : ∀ a ∈ l, a ∈ π.A

def apply (π : PlanProblem) (a : Action π.F) (s : Finsubset π.F) : Option (Finsubset π.F) :=
  if a.Pre ⊆ s then some ((s \ a.Del) ∪ a.Add) else none

--Plan validity defines the semantics of what it means to be a plan.
def ValidPlan (π : PlanProblem) (p : Plan π) : Prop :=
  let rec loop (π : PlanProblem) (s : State π) : Plan π -> Prop
    | ⟨[], _⟩  => s ∈ π.G
    | ⟨a::l, h⟩ =>
      match apply π a s with
      | none    => False
      | some s' =>
        let p' := ⟨l, λa' h'=> by simp [h a' (List.mem_cons_of_mem _ h')]⟩;
        loop π s' p'
  loop π π.S₀ p

/-
n is the maxium number of steps to search for a plan
-/
def BFS (π : PlanProblem) (n : Nat) : Option (Plan π) := do
  let As := Finset.sort Action.lt π.A
  let S₀ : State π := π.S₀
  for i in [:n] do
    for A in As do
      let s' ← apply π A S₀
      if s' ∈ π.G then
        return some ⟨[A], λa h=> by simp [h]⟩
      else
        let S₀ := s'
