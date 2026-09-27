/-!
# Lists and options

`List α` becomes `LeanList<T>`, immutable and singly linked, and `Option α` becomes `LeanOption<T>`. Lean's own
list functions compile too, from their equation lemmas; a function argument is compiled by specializing the
function to it, so `List.sum` and `List.map (fun x => 2 * x)` work, as long as the lambda uses no local variables.
-/

namespace Showcase

/-- The total of a list, by hand. -/
@[export showcase_total]
def total : List Int → Int
  | [] => 0
  | x :: xs => x + total xs

/-- The total again, with the library's `List.sum`. -/
@[export showcase_lib_sum]
def libSum (xs : List Int) : Int := xs.sum

/-- The two agree on every list. -/
theorem total_eq_sum (xs : List Int) : total xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [total, ih]

/-- How many items. -/
@[export showcase_count]
def count (xs : List Int) : Nat := xs.length

/-- Doubled, then reversed. -/
@[export showcase_rev_double]
def revDouble (xs : List Int) : List Int := (xs.map (fun x => 2 * x)).reverse

/-- Two lists, one after the other. -/
@[export showcase_join]
def join (xs ys : List Int) : List Int := xs ++ ys

/-- The first item, if there is one. -/
@[export showcase_first]
def first (xs : List Int) : Option Int := xs.head?

/-- The largest item, or none for an empty list. -/
@[export showcase_max_of]
def maxOf : List Int → Option Int
  | [] => none
  | x :: xs => match maxOf xs with
    | none => some x
    | some m => some (if x > m then x else m)

/-- The total of 1, 2 and 3 is 6. -/
theorem total_example : total [1, 2, 3] = 6 := by decide

/-- The largest of 3, 7 and 2 is 7. -/
theorem maxOf_example : maxOf [3, 7, 2] = some 7 := by decide

end Showcase
