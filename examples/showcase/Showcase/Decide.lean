/-!
# Decidable propositions

`Decidable p` is the answer to a yes/no question about `p`. Lean 4.33 and 4.34 define it as an inductive type with the
constructors `isTrue` and `isFalse`; Lean 4.35 defines it as a structure around a `Bool` (`Decidable.intro`). These
definitions are written so they mean the same on both, and compile to a plain `bool` on both.
-/

namespace Showcase

/-- A custom decision procedure, built with `isTrue` and `isFalse`. -/
def Even (n : Nat) : Prop := n % 2 = 0

instance (n : Nat) : Decidable (Even n) :=
  if h : n % 2 = 0 then Decidable.isTrue h else Decidable.isFalse h

/-- `decide` on a custom instance. -/
@[export showcase_is_even]
def isEven (n : Nat) : Bool := decide (Even n)

/-- `if` on a decidable proposition from the library. -/
@[export showcase_clamp_to]
def clampTo (hi n : Nat) : Nat := if n ≤ hi then n else hi

/-- A conjunction and a disjunction of decidable propositions. -/
@[export showcase_in_band]
def inBand (lo hi n : Nat) : Bool := decide (lo ≤ n ∧ n ≤ hi) || decide (n = 0)

/-- Matching on the decision itself, which is `Decidable.casesOn` on either shape. -/
@[export showcase_sign]
def sign (n : Int) : Nat :=
  match (inferInstance : Decidable (n < 0)) with
  | .isTrue _ => 0
  | .isFalse _ => if n = 0 then 1 else 2

/-- A decision passed around as a value. -/
def both (p q : Prop) [dp : Decidable p] [dq : Decidable q] : Bool := decide p && decide q

@[export showcase_even_and_small]
def evenAndSmall (n : Nat) : Bool := both (Even n) (n < 100)

theorem isEven_four : isEven 4 = true := by decide
theorem sign_neg : sign (-3) = 0 := by decide

end Showcase
