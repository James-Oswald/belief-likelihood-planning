
import src.Finset

structure Action (F : Finset String) where
  Name : String
  Pre : Finsubset F
  Add : Finsubset F
  Del : Finsubset F
deriving BEq

/- A Classical Planning Problem -/
structure PlanProblem where
  F : Finset String         -- the set of facts
  A : Finset (Action F)     -- the set of actions
  S₀ : Finsubset F          -- the initial state
  G : Finset (Finsubset F)

-- A plan for a planning problem π is a list of actions
-- that are all in π.A
structure Plan (π : PlanProblem) where
  l : List (Action π.F)
  h : ∀ a ∈ l, a ∈ π.A

--Plan validity defines the semantics of what it means to be a plan.
def ValidPlan (π : PlanProblem) (p : Plan π) : Prop :=
  let rec loop (π : PlanProblem) (p : Plan π) (s : Finsubset π.F) : Prop :=
    match p with
    | ⟨[], _⟩  => s ∈ π.G
    | ⟨a::l, h⟩ =>
      let s' := (s \ a.Del) ∪ a.Add; -- New state
      let p' := ⟨l, λa' h'=> by simp [h a' (List.mem_cons_of_mem _ h')]⟩; -- Rest of plan
      if a.Pre ⊆ s then loop π p' s' else False
  loop π p π.S₀
