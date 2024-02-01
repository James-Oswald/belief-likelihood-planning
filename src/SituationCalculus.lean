
/-
Followling https://ai.stanford.edu/~epacuit/socsit/lakemeyer.pdf
-/

import src.LogicSymbols

/- Objects -/
inductive Object
  | Var : String -> Object
  | Term : String -> List Object -> Object

/- Actions are ... -/
inductive Action
  | Var : String -> Action
  | Term : String -> List Object -> Action

/- Situations are understood as histories of actions
starting in an initial situation denoted
by the constant S0 -/
def SituationIdent := String
inductive Situation
  | S₀ : Situation
  /- A special binary function do(a, s) is used to
  refer to the situation which results from performing
  action a in s. -/
  | Do : Action -> Situation -> Situation
  | Var : SituationIdent -> Situation
  | Term : SituationIdent -> List Object -> Situation

def DoAction := Sum (List Action) Action
instance : Coe (List Action) DoAction := ⟨Sum.inl⟩
instance : Coe Action DoAction := ⟨Sum.inr⟩

/- To enhance readability, we will sometimes write
do([a1, . . . , an], s) instead of
do(an, do(an−1, . . . , do(a1, S0). . .) -/
def Do (as : DoAction) (si : Situation) : Situation :=
match as with
| Sum.inl as => as.foldl (fun sn a => Situation.Do a sn) si
| Sum.inr a => Situation.Do a si

/- The type of situation calculus formulae -/
inductive Formula
  /- The logical connectives are ¬, ∧, and ∀ -/
  | Not : Formula -> Formula
  | And : Formula -> Formula -> Formula
  | Forall : String -> Formula -> Formula
  /-
  Fluents are used to talk about what is true at
  a given situation. These are simply predicates
  and functions whose last argument is a
  situation term.
  -/
  | Fluent : String -> List Object -> Situation -> Formula
  /- There are two special predicates Poss(a, s),
  indicating that action a is possible in situation s,
  and s ⊏ s', which says that s precedes s', that is, s'
  can be reached from s by a sequence of actions-/
  | Poss : Action -> Situation -> Formula
  | Precedes : Situation -> Situation -> Formula
  /- Equalitues -/
  | ObjectEq : Object -> Object -> Formula
  | SituationEq : Situation -> Situation -> Formula
  | ActionEq : Action -> Action -> Formula

/- Notation Definitions -/
instance : Lnot Formula := ⟨Formula.Not⟩
instance : Land Formula := ⟨Formula.And⟩
instance : Lforall String Formula := ⟨Formula.Forall⟩
/- So i can write things like ∀["x", "y"].[...] -/
instance : Lforall (List String) Formula :=
  ⟨fun xs f => xs.foldr (fun x f => Formula.Forall x f) f⟩

instance : Lor Formula := ⟨fun p q => ¬((¬p) ∧ ¬q)⟩
instance : Lif Formula := ⟨fun p q => (¬p) ∨ q⟩
instance : Liff Formula := ⟨fun p q => (p ⊃ q) ∧ (q ⊃ p)⟩
instance : Lexists String Formula := ⟨fun x f => ¬(∀x.[¬f])⟩
instance : Lexists (List String) Formula := ⟨fun xs f => ¬(∀xs.[¬f])⟩

infixr:80 "=ₛ" => Formula.SituationEq
infixr:80 "=ₐ" => Formula.ActionEq
infixr:80 "=ₒ" => Formula.ObjectEq

infixr:80 "⊏" => Formula.Precedes
infixr:80 "⊑" => fun s1 s2 => s2 ⊏ s1 ∨ s1 =ₛ s2

namespace Example1
  def WithinReach (x : Object) (s : Situation) : Formula :=
    Formula.Fluent "WithinReach" [x] s

  def Holding (x : Object) (s : Situation) : Formula :=
    Formula.Fluent "Holding" [x] s

  def pickup (x : Object) : Action := Action.Term "Pickup" [x]

  def x : Object := Object.Var "x"
  def s : Situation := Situation.Var "s"
  def a : Action := Action.Var "a"

  def PickupAxiom : Formula :=
  ∀["x","s","a"].[((WithinReach x s) ∧ a =ₐ (pickup x)) ⊃ (Holding x (Do a s))]

end Example1
