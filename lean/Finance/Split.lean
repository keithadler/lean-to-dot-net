/-!
# Splitting money, proved

Split a $100.00 bill three ways and the obvious code, `total / 3` each, charges $99.99: a cent disappears.
Round each share instead and you can get $100.02. Every billing system has to decide who pays the extra cents,
and every one has at some point shipped a split that did not add up.

`splitEven` works in cents. It gives the first `total % n` people one cent more than the rest, and this file
proves what an auditor would ask: there are exactly `n` shares, they add up to exactly the total (refunds, which
are negative, included), and no share differs from another by more than a cent.
-/

namespace Finance

/-- `k` shares of `q + 1` followed by `n - k` shares of `q`, when `k ≤ n`. -/
def splitAux (q : Int) : Nat → Nat → List Int
  | _, 0 => []
  | 0, n + 1 => q :: splitAux q 0 n
  | k + 1, n + 1 => (q + 1) :: splitAux q k n

/-- Split `total` cents into `n` shares that add up to exactly `total` and differ by at most one cent: the first
`total % n` shares get the extra cent. Negative totals, refunds, split the same way. Zero shares is the empty
list. -/
@[export lean2il_finance_split_even]
def splitEven (total : Int) (n : Nat) : List Int :=
  splitAux (total / n) (total % n).toNat n

theorem splitAux_length (q : Int) (k n : Nat) : (splitAux q k n).length = n := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih => cases k <;> simp [splitAux, ih]

theorem splitAux_sum (q : Int) (k n : Nat) (h : k ≤ n) : (splitAux q k n).sum = n * q + k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this; simp [splitAux]
  | succ n ih =>
    cases k with
    | zero => simp [splitAux, ih 0 (Nat.zero_le _), Int.add_mul]; omega
    | succ k => simp [splitAux, ih k (by omega), Int.add_mul]; omega

theorem splitAux_fair (q : Int) (k n : Nat) : ∀ x ∈ splitAux q k n, x = q ∨ x = q + 1 := by
  induction n generalizing k with
  | zero => cases k <;> simp [splitAux]
  | succ n ih =>
    cases k with
    | zero => intro x hx; simp [splitAux] at hx; rcases hx with rfl | hx; exact .inl rfl; exact ih 0 x hx
    | succ k => intro x hx; simp [splitAux] at hx; rcases hx with rfl | hx; exact .inr rfl; exact ih k x hx

/-- **Everyone gets a share.** There are exactly `n` of them. -/
theorem splitEven_length (total : Int) (n : Nat) : (splitEven total n).length = n :=
  splitAux_length _ _ _

/-- **Not a cent lost or invented.** For any number of people, the shares add up to exactly the total, refunds
included. -/
theorem splitEven_sum (total : Int) (n : Nat) (hn : 0 < n) : (splitEven total n).sum = total := by
  unfold splitEven
  have hq : (0 : Int) < n := by omega
  have h0 : 0 ≤ total % n := Int.emod_nonneg _ (by omega)
  have h1 : total % n < n := Int.emod_lt_of_pos _ hq
  have hdm : total % n + n * (total / n) = total := ((Int.ediv_emod_unique hq).mp ⟨rfl, rfl⟩).1
  rw [splitAux_sum _ _ _ (by omega)]
  omega

/-- **Fair to the cent.** Every share is the total divided by `n`, rounded down, or one cent more. -/
theorem splitEven_fair (total : Int) (n : Nat) :
    ∀ x ∈ splitEven total n, x = total / n ∨ x = total / n + 1 :=
  splitAux_fair _ _ _

/-- A $100.00 bill split three ways: $33.34, $33.33, $33.33. -/
theorem splitEven_example : splitEven 10000 3 = [3334, 3333, 3333] := by decide

/-- A $100.00 refund split three ways: -$33.33, -$33.33, -$33.34. -/
theorem splitEven_refund_example : splitEven (-10000) 3 = [-3333, -3333, -3334] := by decide

/-- A penny split four ways. -/
theorem splitEven_penny_example : splitEven 1 4 = [1, 0, 0, 0] := by decide

end Finance
