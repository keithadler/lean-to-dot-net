/-!
# Arrays

`Array α` compiles to `LeanArray<T>`, backed by a .NET array: `a[i]` and `a.size` take constant time, and building an
array with `push` is linear, as it is in Lean. A C# caller passes an ordinary `T[]`.

`Array.foldl`, `filter`, `reverse` and `contains` are not special-cased. They are Lean's own recursive definitions,
compiled from the equation lemmas Lean proves for them, over the constant-time `size`, `get` and `push`. `map` and
`range` go through private helpers whose equations cannot be named from outside the library, so lean2il has Lean
prove a restatement over lists (`Array.map f xs = (xs.toList.map f).toArray`) and compiles that.
-/

namespace Showcase

/-- The sum of the items. -/
@[export showcase_array_sum]
def arraySum (xs : Array Int) : Int := xs.foldl (· + ·) 0

/-- Each item replaced by the sum of the items up to and including it. -/
@[export showcase_running_totals]
def runningTotals (xs : Array Int) : Array Int :=
  (xs.foldl (fun (acc, out) x => (acc + x, out.push (acc + x))) ((0 : Int), (#[] : Array Int))).2

/-- How many of `xs` fall in each of `buckets` buckets; values past the last bucket are not counted. -/
@[export showcase_histogram]
def histogram (buckets : Nat) (xs : List Nat) : Array Nat :=
  xs.foldl (fun h x => if hx : x < h.size then h.set x (h[x] + 1) else h) (Array.replicate buckets 0)

/-- The items that are even. -/
@[export showcase_evens]
def evens (xs : Array Int) : Array Int := xs.filter (· % 2 == 0)

/-- Where `k` is in the sorted array `xs`, if it is there: binary search, with the midpoint that does not overflow. -/
@[export showcase_binary_search]
def binarySearch (xs : Array Int) (k : Int) : Option Nat :=
  go 0 xs.size
where
  go (lo hi : Nat) : Option Nat :=
    if h : lo < hi then
      let mid := lo + (hi - lo) / 2
      let x := xs[mid]!
      if x = k then some mid
      else if x < k then go (mid + 1) hi
      else go lo mid
    else none
  termination_by hi - lo

/-- Every item times `k`. -/
@[export showcase_scale_all]
def scaleAll (k : Int) (xs : Array Int) : Array Int := xs.map (· * k)

/-- The items in reverse order. -/
@[export showcase_reversed]
def reversed (xs : Array Int) : Array Int := xs.reverse

/-- The squares of `0` to `n - 1`. -/
@[export showcase_squares]
def squares (n : Nat) : Array Nat := (Array.range n).map (fun i => i * i)

/-- Each item of `xs` beside the item of `ys` at the same place, as long as both last. -/
@[export showcase_pair_up]
def pairUp (xs ys : Array Int) : Array (Int × Int) := xs.zip ys

/-- Whether any item is over `limit`. -/
@[export showcase_any_over]
def anyOver (limit : Int) (xs : Array Int) : Bool := xs.any (· > limit)

/-- The item at `i`, if there is one. -/
@[export showcase_item_at]
def itemAt (xs : Array Int) (i : Nat) : Option Int := xs[i]?

/-- The 8-bit checksum of some bytes: their sum, wrapping at 256. -/
@[export showcase_checksum]
def checksum (data : Array UInt8) : UInt8 := data.foldl (· + ·) 0

theorem histogram_size_aux (xs : List Nat) (h : Array Nat) :
    (xs.foldl (fun h x => if hx : x < h.size then h.set x (h[x] + 1) else h) h).size = h.size := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih => rw [List.foldl, ih]; split <;> simp

/-- **One count per bucket.** The histogram has exactly `buckets` entries, whatever the input. -/
theorem histogram_size (buckets : Nat) (xs : List Nat) : (histogram buckets xs).size = buckets := by
  unfold histogram; rw [histogram_size_aux]; simp

/-- Three items sum to six. -/
theorem arraySum_example : arraySum #[1, 2, 3] = 6 := by decide

/-- Running totals of 1, 2, 3. -/
theorem runningTotals_example : runningTotals #[1, 2, 3] = #[1, 3, 6] := by decide

/-- A zero and two ones in three buckets; 3 and 7 are past the last bucket. -/
theorem histogram_example : histogram 3 [1, 3, 0, 1, 7] = #[1, 2, 0] := by decide

/-- 7 is at index 3. -/
theorem binarySearch_example : binarySearch #[1, 3, 5, 7, 9] 7 = some 3 := by
  simp [binarySearch, binarySearch.go]

/-- The first four squares. -/
theorem squares_example : squares 4 = #[0, 1, 4, 9] := by apply Array.toList_inj.mp; simp [squares, List.range_succ]

/-- Reversing three items. -/
theorem reversed_example : reversed #[1, 2, 3] = #[3, 2, 1] := by simp [reversed]

/-- 200 + 100 wraps to 44. -/
theorem checksum_example : checksum #[200, 100] = 44 := by decide

end Showcase
