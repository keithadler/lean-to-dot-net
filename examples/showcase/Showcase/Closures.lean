/-!
# Lambdas that use local variables

A function argument that uses local variables is compiled by specializing the function it is passed to, with
those variables as extra parameters: `xs.map (fun x => x + k)` becomes a copy of `List.map` that takes `k`. No
delegates, no allocation per call, and the recursion is compiled from the same proved equations as before.
-/

namespace Showcase

/-- Add `k` to every item. -/
@[export showcase_add_all]
def addAll (k : Int) (xs : List Int) : List Int := xs.map (fun x => x + k)

/-- The items strictly between `lo` and `hi`. -/
@[export showcase_between]
def between (lo hi : Int) (xs : List Int) : List Int := xs.filter (fun x => lo < x && x < hi)

/-- The sum of the items, each capped at `cap`. -/
@[export showcase_capped_sum]
def cappedSum (cap : Int) (xs : List Int) : Int := xs.foldl (fun acc x => acc + (if x > cap then cap else x)) 0

/-- Scale by `num / den`, rounding each result down: two captured variables. -/
@[export showcase_scale]
def scale (num den : Int) (xs : List Int) : List Int := xs.map (fun x => x * num / den)

/-- Adding k to each item adds k times the length to the sum. -/
theorem addAll_sum (k : Int) (xs : List Int) : (addAll k xs).sum = xs.sum + k * xs.length := by
  induction xs with
  | nil => simp [addAll]
  | cons x xs ih => simp [addAll, List.map] at *; rw [ih]; simp [Int.mul_add]; omega

/-- A worked example. -/
theorem addAll_example : addAll 10 [1, 2, 3] = [11, 12, 13] := by decide

/-- A worked example. -/
theorem between_example : between 2 6 [1, 3, 5, 7] = [3, 5] := by decide

end Showcase
