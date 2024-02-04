
import src.Finset

structure Action (Facts : Finset String) where
  Name: String
  Pre : Finsubset Facts
  Add : Finsubset Facts
  Del : Finsubset Facts

/- A Classical Planning Problem -/
structure CPP where
  Facts : Finset String
  Actions : Finset (Action Facts)
  --Action names are unique
  actions_nodup : List.Nodup ActionNames
  Init : Finsubset Facts
  Goals : Finset (Finsubset Facts)

def CPP.ActionNames (π : CPP) : Finset String :=
  π.Actions.map Action.Name

--def Plan (π : CPP) : Type := List Action (Facts π)
