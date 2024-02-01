/-
The file defines typeclasses and notations for
logical operators, it is based off a
discussion I've had on Zulip with
Eric Weiser. Operators are ordered by precedence
-/

class Forces (α : Type u) (β : Type v) : Type (max u v) where
  forces : α → β → Prop

infix:30 "⊩" => Forces.forces
infix:30 "⊮" => ¬(Forces.forces · ·)

--For biconditional ↔
class Liff (α : Type) : Type where
  liff : α → α → α

infix:50 "↔" => Liff.liff
infix:50 "≡" => Liff.liff

--For material implication ⊃
class Lif (α : Type) : Type where
  lif : α → α → α

infixl:55 "⊃" => Lif.lif

--For logical or ∨
class Lor (α : Type) : Type where
  lor : α → α → α

infixr:60 "∨" => Lor.lor

--For logical and ∧
class Land (α : Type) : Type where
  land : α → α → α

infixr:65 "∧"  => Land.land

class Lforall (α β: Type) : Type where
  lforall : α → β → β

notation "∀" x:70 ".(" P:0 ")"  => Lforall.lforall x P
notation "∀" x:70 ".[" P:0 "]"  => Lforall.lforall x P

class Lexists (α β: Type) : Type where
  lexists : α → β → β

notation "∃" x:70 ".(" P:0 ")"  => Lexists.lexists x P
notation "∃" x:70 ".[" P:0 "]"  => Lexists.lexists x P

--For not ¬
class Lnot (α : Type) : Type where
  lnot : α → α

notation:max "¬" a:70 => Lnot.lnot a

--For box □
class Box (α : Type) : Type where
  box : α → α

notation:max "□" a:70 => Box.box a

--For diamond ⋄
class Diamond (α : Type) : Type where
  diamond : α → α

notation:max "⋄" a:70 => Diamond.diamond a
