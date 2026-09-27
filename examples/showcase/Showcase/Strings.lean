/-!
# Strings

`String` becomes `System.String`. Lean counts a string's length in Unicode code points, not UTF-16 units, and so
does the compiled code: `"a😀b"` has length 3 in both, where .NET's `Length` says 4.
-/

namespace Showcase

/-- A greeting that counts. -/
@[export showcase_greet]
def greet (name : String) (n : Nat) : String := "hello " ++ name ++ ", you are number " ++ toString n

/-- Length in characters, as Lean counts them. -/
@[export showcase_chars]
def chars (s : String) : Nat := s.length

/-- A worked greeting. -/
theorem greet_example : greet "Ada" 7 = "hello Ada, you are number 7" := by decide

end Showcase
