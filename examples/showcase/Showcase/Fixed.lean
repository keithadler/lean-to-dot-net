/-!
# Fixed-width integers

`UInt8` ... `UInt64` and `Int8` ... `Int64` compile to `byte` ... `ulong` and `sbyte` ... `long`: the same bits, so a
C# caller passes and gets back ordinary integers. Arithmetic wraps, as it does in C#. Where Lean and C# disagree,
the compiled code does what Lean does: dividing by zero gives zero instead of throwing, and a shift by 65 is a shift
by 1, since the count wraps around the width.

The classic bug is here too. `(lo + hi) / 2` is the midpoint of a binary search until `lo + hi` passes
`Int32.MaxValue` and wraps negative, which went unnoticed in the JDK's binary search for nine years. `midpoint` is
the fixed version, and the theorem below is the proof that it stays between `lo` and `hi`.
-/

namespace Showcase

/-- The 64-bit FNV-1a hash of some bytes: xor each byte in, multiply by the FNV prime, and let it wrap. -/
@[export showcase_fnv1a]
def fnv1a (bytes : List UInt8) : UInt64 :=
  bytes.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

/-- Add two bytes, stopping at 255 instead of wrapping around to small numbers. -/
@[export showcase_saturating_add]
def saturatingAdd (a b : UInt8) : UInt8 :=
  if a.toNat + b.toNat > 255 then 255 else a + b

/-- Rotate the bits of `x` left by `n`. -/
@[export showcase_rotate_left]
def rotateLeft (x n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- The midpoint of `lo` and `hi` without overflow: `lo + (hi - lo) / 2`, for `0 ≤ lo ≤ hi`. -/
@[export showcase_midpoint]
def midpoint (lo hi : Int32) : Int32 :=
  lo + (hi - lo) / 2

/-- The midpoint everyone writes first, which wraps negative when `lo + hi` passes `Int32.MaxValue`. -/
@[export showcase_naive_midpoint]
def naiveMidpoint (lo hi : Int32) : Int32 :=
  (lo + hi) / 2

/-- An `Int` as an `Int32`, clamped to the range instead of wrapped. -/
@[export showcase_clamp_to_int32]
def clampToInt32 (x : Int) : Int32 :=
  if x > 2147483647 then 2147483647 else if x < -2147483648 then -2147483648 else Int32.ofInt x

/-- The FNV-1a hash of no bytes is the offset basis. -/
theorem fnv1a_empty : fnv1a [] = 14695981039346656037 := by decide

/-- 200 + 100 saturates at 255 instead of wrapping to 44. -/
theorem saturatingAdd_example : saturatingAdd 200 100 = 255 := by decide

/-- Rotating the top bit left by one brings it around to the bottom. -/
theorem rotateLeft_example : rotateLeft 0x80000001 1 = 3 := by decide

/-- Near the top of the range the midpoint is still right. -/
theorem midpoint_example : midpoint 2000000000 2100000000 = 2050000000 := by decide

/-- The naive midpoint of the same two numbers wraps negative. -/
theorem naiveMidpoint_example : naiveMidpoint 2000000000 2100000000 = -97483648 := by decide

/-- A big `Int` clamps to `Int32.MaxValue`. -/
theorem clampToInt32_example : clampToInt32 10000000000 = 2147483647 := by decide

/-- **Saturation never wraps.** The saturated sum is at least each input. -/
theorem saturatingAdd_ge (a b : UInt8) : a ≤ saturatingAdd a b := by
  unfold saturatingAdd
  split
  · exact UInt8.le_iff_toNat_le.mpr (by have := a.toNat_lt; simp; omega)
  · rename_i h
    exact UInt8.le_iff_toNat_le.mpr (by rw [UInt8.toNat_add]; omega)

/-- **The midpoint stays in range.** For `0 ≤ lo ≤ hi` it is between them, where the naive one can go negative. -/
theorem midpoint_between (lo hi : Int32) (h0 : 0 ≤ lo) (h : lo ≤ hi) :
    lo ≤ midpoint lo hi ∧ midpoint lo hi ≤ hi := by
  unfold midpoint
  simp only [Int32.le_iff_toInt_le] at *
  have z : Int32.toInt 0 = 0 := rfl
  have two : Int32.toInt 2 = 2 := rfl
  have hl := lo.le_toInt
  have hh := hi.toInt_le
  have mx : Int32.maxValue.toInt = 2 ^ 31 - 1 := rfl
  rw [z] at h0
  rw [mx] at hh
  have hsub : (hi - lo).toInt = hi.toInt - lo.toInt := by
    rw [Int32.toInt_sub]; rw [Int.bmod_eq_of_le] <;> omega
  have hq : (hi.toInt - lo.toInt).tdiv 2 = (hi.toInt - lo.toInt) / 2 :=
    Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hdiv : ((hi - lo) / 2).toInt = (hi.toInt - lo.toInt) / 2 := by
    rw [Int32.toInt_div, hsub, two, hq]; rw [Int.bmod_eq_of_le] <;> omega
  have hadd : (lo + (hi - lo) / 2).toInt = lo.toInt + (hi.toInt - lo.toInt) / 2 := by
    rw [Int32.toInt_add, hdiv]; rw [Int.bmod_eq_of_le] <;> omega
  rw [hadd]
  omega

end Showcase
