/-!
# Rounding money, proved

.NET's `Math.Round(decimal)` rounds a midpoint to the nearest even digit unless you say otherwise, so
`Math.Round(0.125m, 2)` is `0.12`, not the `0.13` an invoice expects. `Math.Round(1.005, 2,
MidpointRounding.AwayFromZero)` on a `double` is `1`, because the `double` nearest to 1.005 sits just
below it; of the 10,000 prices from `0.005` to `99.995` that end in a half cent, 572 round the wrong way
as doubles on .NET 10. And the hand-rolled fix, `Math.Floor(x * 100 + 0.5) / 100`, rounds a refund of
`-2.675` to `-2.67` while the sale rounds to `2.68`.

This file defines rounding on exact decimals, a mantissa and a scale like `System.Decimal`, and proves
what it does: the result is within half a unit of the last kept digit, a midpoint goes where the mode
says, a refund rounds to the negative of its sale, and a value already at the precision is left alone.
The functions marked `@[export]` are compiled to a .NET assembly by `lean2il`, which re-checks every
proof here with Tenet first.
-/

namespace Finance

/-- How to settle a value that is not already at the requested precision. The five cases are .NET's
`MidpointRounding`, in its order, with the same meaning: the first two only decide exact midpoints and
otherwise round to nearest; the last three are directed and ignore midpoints altogether. -/
inductive RoundingMode where
  /-- Nearest; a midpoint goes to the even neighbor. Banker's rounding, and .NET's default. -/
  | toEven
  /-- Nearest; a midpoint goes away from zero. What invoices, tax forms and most people expect. -/
  | awayFromZero
  /-- Toward zero: truncate. -/
  | toZero
  /-- Toward negative infinity: floor. -/
  | toNegativeInfinity
  /-- Toward positive infinity: ceiling. -/
  | toPositiveInfinity
  deriving DecidableEq, Repr

/-- Divide `m` by `q` and round the quotient to an integer by `mode`. Every rounding in this file is this
one function: to round a decimal to `d` digits, divide its mantissa by `10 ^ (scale - d)`. -/
def roundDiv (m : Int) (q : Nat) (mode : RoundingMode) : Int :=
  let f := m / (q : Int)
  let r := m % (q : Int)
  match mode with
  | .toNegativeInfinity => f
  | .toPositiveInfinity => if r = 0 then f else f + 1
  | .toZero => if r ≠ 0 ∧ m < 0 then f + 1 else f
  | .awayFromZero =>
    if 2 * r < q then f else if 2 * r > q then f + 1 else if m < 0 then f else f + 1
  | .toEven =>
    if 2 * r < q then f else if 2 * r > q then f + 1 else if f % 2 = 0 then f else f + 1

/-- An exact decimal number, `mantissa × 10 ^ (-scale)`, the same shape as `System.Decimal` without its
96-bit limit. `lean2il` passes a .NET `decimal` in and out of any function over `Dec`. -/
structure Dec where
  /-- The digits, as an integer. `2.675` is mantissa `2675`. -/
  mantissa : Int
  /-- How many of those digits are after the decimal point. `2.675` is scale `3`. -/
  scale : Nat
  deriving DecidableEq, Repr

/-- Round `x` to `digits` decimal places by `mode`, as `Math.Round(x, digits, mode)` does for a `decimal`.
A value with no more than `digits` places comes back unchanged.

Proved below: the result is within half a unit of its last digit for the two midpoint modes
(`round_error_le_half`), a midpoint goes where the mode says (`round_tie_awayFromZero`,
`round_tie_toEven`), `round (-x) = -(round x)` for the symmetric modes (`round_neg`), and rounding
twice to the same precision is rounding once (`round_round`). -/
@[export lean2il_finance_round]
def round (x : Dec) (digits : Nat) (mode : RoundingMode) : Dec :=
  if x.scale ≤ digits then x
  else ⟨roundDiv x.mantissa (10 ^ (x.scale - digits)) mode, digits⟩

/-- Round to cents with midpoints away from zero: the rule on an invoice. -/
@[export lean2il_finance_round_cents]
def roundCents (x : Dec) : Dec := round x 2 .awayFromZero

instance : Neg Dec := ⟨fun x => ⟨-x.mantissa, x.scale⟩⟩

@[simp] theorem neg_mantissa (x : Dec) : (-x).mantissa = -x.mantissa := rfl
@[simp] theorem neg_scale (x : Dec) : (-x).scale = x.scale := rfl

/-! ## Division with remainder, the facts everything below rests on -/

private theorem divMod (m q : Int) (hq : 0 < q) : m % q + q * (m / q) = m ∧ 0 ≤ m % q ∧ m % q < q :=
  (Int.ediv_emod_unique hq).mp ⟨rfl, rfl⟩

/-- The sign of a multiple of `q`, in the form `omega` can use: `q * f` is `0`, at least `q`, or at most `-q`. -/
private theorem mulSign (q f : Int) (hq : 0 < q) :
    (f ≤ -1 → q * f ≤ -q) ∧ (f = 0 → q * f = 0) ∧ (1 ≤ f → q ≤ q * f) := by
  refine ⟨fun h => ?_, fun h => by simp [h], fun h => ?_⟩
  · have : q * f ≤ q * (-1) := Int.mul_le_mul_of_nonneg_left h (by omega)
    omega
  · have : q * 1 ≤ q * f := Int.mul_le_mul_of_nonneg_left h (by omega)
    omega

private theorem neg_div_exact (m q : Int) (hq : 0 < q) (h : m % q = 0) :
    (-m) / q = -(m / q) ∧ (-m) % q = 0 := by
  have ⟨h1, _, _⟩ := divMod m q hq
  apply (Int.ediv_emod_unique hq).mpr
  rw [Int.mul_neg]; omega

private theorem neg_div_inexact (m q : Int) (hq : 0 < q) (h : m % q ≠ 0) :
    (-m) / q = -(m / q) - 1 ∧ (-m) % q = q - m % q := by
  have ⟨h1, h2, h3⟩ := divMod m q hq
  apply (Int.ediv_emod_unique hq).mpr
  rw [Int.mul_sub, Int.mul_neg, Int.mul_one]; omega

/-- After `roundDiv` is unfolded: name the floor `f` and remainder `r` of `m / q`, give `omega` what it
needs to know about them, split every branch, and let `omega` close each one. -/
local macro "div_cases" m:term:max q:term:max : tactic => `(tactic| (
  have hdm := divMod $m $q (by omega)
  have hsg := mulSign $q ($m / $q) (by omega)
  have hsg1 := mulSign $q ($m / $q + 1) (by omega)
  rw [Int.mul_add, Int.mul_one] at hsg1
  generalize $m / $q = f at *
  generalize $m % $q = r at *
  repeat' split
  all_goals (try rw [Int.mul_add, Int.mul_one]); omega))

/-! ## What each mode does -/

/-- The result is always the floor of `m / q` or one more. -/
theorem roundDiv_floor_or_succ (m : Int) (q : Nat) (mode : RoundingMode) :
    roundDiv m q mode = m / q ∨ roundDiv m q mode = m / q + 1 := by
  cases mode <;> simp only [roundDiv] <;> repeat' split
  all_goals first | omega | simp

/-- Floor: the largest multiple of `q` not above `m`. -/
theorem roundDiv_toNegativeInfinity (m : Int) (q : Nat) (hq : 0 < q) :
    q * roundDiv m q .toNegativeInfinity ≤ m ∧ m < q * roundDiv m q .toNegativeInfinity + q := by
  simp only [roundDiv]; div_cases m (q : Int)

/-- Ceiling: the smallest multiple of `q` not below `m`. -/
theorem roundDiv_toPositiveInfinity (m : Int) (q : Nat) (hq : 0 < q) :
    q * roundDiv m q .toPositiveInfinity - q < m ∧ m ≤ q * roundDiv m q .toPositiveInfinity := by
  simp only [roundDiv]; div_cases m (q : Int)

/-- Truncation: never further from zero than `m`, and less than one step closer. -/
theorem roundDiv_toZero (m : Int) (q : Nat) (hq : 0 < q) :
    (q * roundDiv m q .toZero).natAbs ≤ m.natAbs ∧ m.natAbs < (q * roundDiv m q .toZero).natAbs + q := by
  simp only [roundDiv]; div_cases m (q : Int)

/-- Away from zero is within half a step of `m`, and on an exact midpoint it takes the neighbor further
from zero: a non-negative `m` rounds up, a negative one rounds down. -/
theorem roundDiv_awayFromZero (m : Int) (q : Nat) (hq : 0 < q) :
    (0 ≤ m → -(q : Int) ≤ 2 * (m - q * roundDiv m q .awayFromZero) ∧ 2 * (m - q * roundDiv m q .awayFromZero) < q) ∧
    (m < 0 → -(q : Int) < 2 * (m - q * roundDiv m q .awayFromZero) ∧ 2 * (m - q * roundDiv m q .awayFromZero) ≤ q) := by
  simp only [roundDiv]; div_cases m (q : Int)

/-- To even is within half a step of `m`, and on an exact midpoint the result is even. -/
theorem roundDiv_toEven (m : Int) (q : Nat) (hq : 0 < q) :
    -(q : Int) ≤ 2 * (m - q * roundDiv m q .toEven) ∧ 2 * (m - q * roundDiv m q .toEven) ≤ q ∧
    ((2 * (m - q * roundDiv m q .toEven) = q ∨ 2 * (m - q * roundDiv m q .toEven) = -(q : Int)) →
      roundDiv m q .toEven % 2 = 0) := by
  simp only [roundDiv]; div_cases m (q : Int)

/-- The two midpoint modes are nearest-integer rounding: no multiple of `q` is closer to `m`. -/
theorem roundDiv_nearest (m : Int) (q : Nat) (hq : 0 < q) (mode : RoundingMode)
    (hmode : mode = .toEven ∨ mode = .awayFromZero) (k : Int) :
    (m - q * roundDiv m q mode).natAbs ≤ (m - q * k).natAbs := by
  have hhalf : -(q : Int) ≤ 2 * (m - q * roundDiv m q mode) ∧ 2 * (m - q * roundDiv m q mode) ≤ q := by
    rcases hmode with rfl | rfl
    · have := roundDiv_toEven m q hq; omega
    · have := roundDiv_awayFromZero m q hq; omega
  generalize roundDiv m q mode = n at hhalf
  rcases Int.lt_trichotomy k n with h | h | h
  · have : (q : Int) * (k + 1) ≤ q * n := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [Int.mul_add, Int.mul_one] at this; omega
  · subst h; omega
  · have : (q : Int) * (n + 1) ≤ q * k := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [Int.mul_add, Int.mul_one] at this; omega

/-- Off a midpoint, banker's rounding and away-from-zero agree. They differ only on exact ties. -/
theorem roundDiv_toEven_eq_awayFromZero (m : Int) (q : Nat) (h : 2 * (m % q) ≠ q) :
    roundDiv m q .toEven = roundDiv m q .awayFromZero := by
  simp only [roundDiv]
  repeat' split
  all_goals omega

/-- A refund rounds to the negative of its sale, for every mode that treats signs alike. Floor and
ceiling do not: they trade places instead (`roundDiv_neg_floor`). -/
theorem roundDiv_neg (m : Int) (q : Nat) (hq : 0 < q) (mode : RoundingMode)
    (hmode : mode = .toEven ∨ mode = .awayFromZero ∨ mode = .toZero) :
    roundDiv (-m) q mode = -roundDiv m q mode := by
  by_cases hr : m % q = 0
  · have ⟨e1, e2⟩ := neg_div_exact m q (by omega) hr
    rcases hmode with rfl | rfl | rfl <;> simp only [roundDiv, e1, e2] <;> clear e1 e2 <;> div_cases m (q : Int)
  · have ⟨e1, e2⟩ := neg_div_inexact m q (by omega) hr
    rcases hmode with rfl | rfl | rfl <;> simp only [roundDiv, e1, e2] <;> clear e1 e2 <;> div_cases m (q : Int)

/-- Floor of a negation is minus the ceiling. -/
theorem roundDiv_neg_floor (m : Int) (q : Nat) (hq : 0 < q) :
    roundDiv (-m) q .toNegativeInfinity = -roundDiv m q .toPositiveInfinity := by
  by_cases hr : m % q = 0
  · have ⟨e1, _⟩ := neg_div_exact m q (by omega) hr
    simp only [roundDiv, e1]; clear e1; div_cases m (q : Int)
  · have ⟨e1, _⟩ := neg_div_inexact m q (by omega) hr
    simp only [roundDiv, e1]; clear e1; div_cases m (q : Int)

/-- A value already a multiple of `q` is left exactly as it is, in every mode. -/
theorem roundDiv_exact (k : Int) (q : Nat) (hq : 0 < q) (mode : RoundingMode) :
    roundDiv (q * k) q mode = k := by
  have e1 : (q * k : Int) / q = k := Int.mul_ediv_cancel_left k (by omega)
  have e2 : (q * k : Int) % q = 0 := Int.mul_emod_right _ _
  cases mode <;> simp only [roundDiv, e1, e2] <;> repeat' split
  all_goals first | omega | simp_all

/-! ## The same facts about `round` on decimals -/

private theorem pow_pos' (d : Nat) : 0 < 10 ^ d := Nat.pow_pos (by decide)

/-- A value with no more than `digits` places is returned unchanged. -/
theorem round_of_scale_le (x : Dec) (digits : Nat) (mode : RoundingMode) (h : x.scale ≤ digits) :
    round x digits mode = x := by
  simp [round, h]

/-- The result has at most `digits` places. -/
theorem round_scale_le (x : Dec) (digits : Nat) (mode : RoundingMode) :
    (round x digits mode).scale ≤ digits := by
  unfold round; split <;> simp_all <;> omega

/-- **Half a unit.** For the two midpoint modes, rounding `x` to `digits` places moves it by at most half
of `10 ^ (-digits)`. Both sides are written at `x`'s scale, `s`, so the claim is about integers:
twice the change in the mantissa is at most `10 ^ (s - digits)`, one unit of the last kept digit. -/
theorem round_error_le_half (x : Dec) (digits : Nat) (mode : RoundingMode)
    (hmode : mode = .toEven ∨ mode = .awayFromZero) (h : digits < x.scale) :
    2 * (x.mantissa - (10 ^ (x.scale - digits) : Nat) * (round x digits mode).mantissa).natAbs
      ≤ 10 ^ (x.scale - digits) := by
  have hq := pow_pos' (x.scale - digits)
  simp only [round, show ¬x.scale ≤ digits by omega, if_false]
  rcases hmode with rfl | rfl
  · have := roundDiv_toEven x.mantissa _ hq; omega
  · have := roundDiv_awayFromZero x.mantissa _ hq; omega

/-- **Nearest.** For the two midpoint modes no other value with `digits` places is closer to `x`. -/
theorem round_nearest (x : Dec) (digits : Nat) (mode : RoundingMode)
    (hmode : mode = .toEven ∨ mode = .awayFromZero) (h : digits < x.scale) (k : Int) :
    (x.mantissa - (10 ^ (x.scale - digits) : Nat) * (round x digits mode).mantissa).natAbs
      ≤ (x.mantissa - (10 ^ (x.scale - digits) : Nat) * k).natAbs := by
  simp only [round, show ¬x.scale ≤ digits by omega, if_false]
  exact roundDiv_nearest _ _ (pow_pos' _) mode hmode k

/-- **Midpoints, away from zero.** When `x` is exactly halfway, the result is the neighbor further from
zero: `0.125` goes to `0.13` and `-0.125` to `-0.13`. -/
theorem round_tie_awayFromZero (x : Dec) (digits : Nat) (h : digits < x.scale)
    (tie : 2 * (x.mantissa % (10 ^ (x.scale - digits) : Nat)) = (10 ^ (x.scale - digits) : Nat)) :
    x.mantissa.natAbs < ((10 ^ (x.scale - digits) : Nat) * (round x digits .awayFromZero).mantissa).natAbs := by
  have hq := pow_pos' (x.scale - digits)
  have := divMod x.mantissa (10 ^ (x.scale - digits) : Nat) (by omega)
  simp only [round, show ¬x.scale ≤ digits by omega, if_false, roundDiv]
  repeat' split
  all_goals (try rw [Int.mul_add, Int.mul_one]); omega

/-- **Midpoints, to even.** When `x` is exactly halfway, the last kept digit is even: `0.125` goes to
`0.12` and `0.135` to `0.14`. -/
theorem round_tie_toEven (x : Dec) (digits : Nat) (h : digits < x.scale)
    (tie : 2 * (x.mantissa % (10 ^ (x.scale - digits) : Nat)) = (10 ^ (x.scale - digits) : Nat)) :
    (round x digits .toEven).mantissa % 2 = 0 := by
  simp only [round, show ¬x.scale ≤ digits by omega, if_false, roundDiv]
  repeat' split
  all_goals omega

/-- **Refunds.** Rounding a negated amount gives the negated rounding, for banker's rounding,
away-from-zero and truncation. `Math.Floor(x * 100 + 0.5) / 100` fails this at every negative midpoint. -/
theorem round_neg (x : Dec) (digits : Nat) (mode : RoundingMode)
    (hmode : mode = .toEven ∨ mode = .awayFromZero ∨ mode = .toZero) :
    round (-x) digits mode = -(round x digits mode) := by
  unfold round
  by_cases h : x.scale ≤ digits
  · simp [h]
  · simp only [neg_scale, h, if_false, neg_mantissa]
    rw [roundDiv_neg _ _ (pow_pos' _) mode hmode]
    rfl

/-- **Once is enough.** Rounding a rounded value to the same precision changes nothing. -/
theorem round_round (x : Dec) (digits : Nat) (mode : RoundingMode) :
    round (round x digits mode) digits mode = round x digits mode :=
  round_of_scale_le _ _ _ (round_scale_le x digits mode)

/-- **Invoices.** Cents are within half a cent of the amount, and a refund rounds to minus its sale. -/
theorem roundCents_spec (x : Dec) :
    (2 < x.scale → 2 * (x.mantissa - (10 ^ (x.scale - 2) : Nat) * (roundCents x).mantissa).natAbs
      ≤ 10 ^ (x.scale - 2)) ∧ roundCents (-x) = -(roundCents x) :=
  ⟨round_error_le_half x 2 .awayFromZero (.inr rfl), round_neg x 2 .awayFromZero (.inr (.inl rfl))⟩

/-! ## The examples from the top of the file, checked -/

/-- `Math.Round(0.125m, 2)` is `0.12`: .NET's default mode is banker's rounding. -/
theorem bankers_default_example : round ⟨125, 3⟩ 2 .toEven = ⟨12, 2⟩ := by decide

/-- With `awayFromZero` the same invoice line is `0.13`. -/
theorem invoice_example : round ⟨125, 3⟩ 2 .awayFromZero = ⟨13, 2⟩ := by decide

/-- As an exact decimal, `1.005` rounds to `1.01`. The `double` nearest to it rounds to `1.00`. -/
theorem decimal_1_005_example : round ⟨1005, 3⟩ 2 .awayFromZero = ⟨101, 2⟩ := by decide

/-- A sale of `2.675` rounds to `2.68`. -/
theorem sale_example : round ⟨2675, 3⟩ 2 .awayFromZero = ⟨268, 2⟩ := by decide

/-- The refund of that sale is `-2.68`, not the `-2.67` of `floor(x * 100 + 0.5) / 100`. -/
theorem refund_example : round ⟨-2675, 3⟩ 2 .awayFromZero = ⟨-268, 2⟩ := by decide

/-- A line of `$19.995` is billed as `$20.00`. -/
theorem roundCents_example : roundCents ⟨19995, 3⟩ = ⟨2000, 2⟩ := by decide

/-- **Double rounding is not rounding.** Rounding `2.4449` to three places and then to two gives `2.45`;
rounding it to two directly gives `2.44`. Round once, from the exact value, at the end. -/
theorem double_rounding_example :
    round (round ⟨24449, 4⟩ 3 .awayFromZero) 2 .awayFromZero ≠ round ⟨24449, 4⟩ 2 .awayFromZero := by
  decide

end Finance
