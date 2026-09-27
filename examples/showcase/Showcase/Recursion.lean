/-!
# Recursion

lean2il compiles a recursive definition from its equation lemma, `f.eq_def : ∀ xs, f xs = rhs`, which Lean proves
and Tenet re-checks. A call to itself in tail position becomes a jump, so loops run in constant stack; any other
recursion that outgrows the thread's stack is rerun, transparently, on a 1 GB one.
-/

namespace Showcase

/-- `0 + 1 + ... + n`, by structural recursion. Not tail recursive: `sumTo 200000` still works. -/
@[export showcase_sum_to]
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- Twice `sumTo n` is `n * (n + 1)`: Gauss, proved. -/
theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo, Nat.mul_add, ih, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

/-- The greatest common divisor, by well-founded recursion. Tail recursive: a loop in the IL. -/
@[export showcase_gcd]
def gcd' (a b : Nat) : Nat := if h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- The sum of the decimal digits of `n`, with an accumulator: a loop. -/
@[export showcase_digit_sum]
def digitSum (n acc : Nat) : Nat := if n = 0 then acc else digitSum (n / 10) (acc + n % 10)
termination_by n
decreasing_by omega

/-- The sum of the first ten is fifty-five. -/
theorem sumTo_example : sumTo 10 = 55 := by decide

end Showcase
