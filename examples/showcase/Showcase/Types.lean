/-!
# Your own data types

A type with several constructors carrying data, or containing itself, becomes an abstract .NET class with a `Tag`
and a sealed nested class per constructor, so C# can `switch` on it with type patterns. A type with parameters is
compiled once per instantiation: `Pair Int String` becomes the class `PairOfIntString`.
-/

namespace Showcase

/-- Arithmetic on integers, as a syntax tree. -/
inductive Arith where
  /-- A literal. -/
  | num (n : Int)
  /-- A variable, looked up in the environment by index. -/
  | var (i : Nat)
  /-- A sum. -/
  | add (a b : Arith)
  /-- A product. -/
  | mul (a b : Arith)

/-- The value of an expression, with variable `i` taken from `env` (zero when out of range). -/
@[export showcase_eval]
def eval (env : List Int) : Arith → Int
  | .num n => n
  | .var i => env.getD i 0
  | .add a b => eval env a + eval env b
  | .mul a b => eval env a * eval env b

/-- Constant folding: `2 + 3` becomes `5`, and `x * 0` becomes `0`. -/
@[export showcase_fold]
def fold : Arith → Arith
  | .num n => .num n
  | .var i => .var i
  | .add a b =>
    match fold a, fold b with
    | .num x, .num y => .num (x + y)
    | a', b' => .add a' b'
  | .mul a b =>
    match fold a, fold b with
    | .num x, .num y => .num (x * y)
    | .num 0, _ => .num 0
    | _, .num 0 => .num 0
    | a', b' => .mul a' b'

/-- **The optimizer is correct.** Folding never changes the value of an expression, in any environment. -/
theorem fold_correct (env : List Int) (e : Arith) : eval env (fold e) = eval env e := by
  induction e with
  | num n => rfl
  | var i => rfl
  | add a b iha ihb =>
    simp only [fold]
    split <;> (simp only [eval]; rw [← iha, ← ihb] <;> (clear iha ihb; simp_all [eval]))
  | mul a b iha ihb =>
    simp only [fold]
    split <;> (simp only [eval]; rw [← iha, ← ihb] <;> (clear iha ihb; simp_all [eval]))

/-- `2 * (x + 3)` with `x = 4` is `14`. -/
theorem eval_example : eval [4] (.mul (.num 2) (.add (.var 0) (.num 3))) = 14 := by decide

/-- A binary search tree of integers. -/
inductive Tree where
  | leaf
  | node (left : Tree) (key : Int) (right : Tree)

/-- Insert a key, keeping the tree ordered; a key already present is left alone. -/
@[export showcase_insert]
def insert (k : Int) : Tree → Tree
  | .leaf => .node .leaf k .leaf
  | .node l x r => if k < x then .node (insert k l) x r else if x < k then .node l x (insert k r) else .node l x r

/-- The keys, in order. -/
@[export showcase_to_list]
def toList : Tree → List Int
  | .leaf => []
  | .node l x r => toList l ++ [x] ++ toList r

/-- Build a tree from a list. -/
@[export showcase_of_list]
def ofList (xs : List Int) : Tree := xs.foldl (fun t x => insert x t) .leaf

/-- Sorting, the tree way: build a search tree and read it back. -/
@[export showcase_tree_sort]
def treeSort (xs : List Int) : List Int := toList (ofList xs)

/-- Whether a key is in the tree. -/
@[export showcase_contains]
def contains (k : Int) : Tree → Bool
  | .leaf => false
  | .node l x r => if k < x then contains k l else if x < k then contains k r else true

/-- Inserting a key makes it present. -/
theorem contains_insert (k : Int) (t : Tree) : contains k (insert k t) = true := by
  induction t with
  | leaf => simp [insert, contains]
  | node l x r ihl ihr =>
    simp only [insert]
    split
    · simp [contains, *]
    · split
      · simp [contains, *]
      · simp [contains, *]

/-- Sorting 3, 1, 2 gives 1, 2, 3. -/
theorem treeSort_example : treeSort [3, 1, 2] = [1, 2, 3] := by decide

/-- A result or an error message. -/
inductive Result where
  | ok (value : Int)
  | error (message : String)

/-- Divide, or say why not. -/
@[export showcase_safe_div]
def safeDiv (a b : Int) : Result :=
  if b = 0 then .error ("cannot divide " ++ toString a ++ " by zero") else .ok (a / b)

/-- Two values of any types. -/
structure Pair (α β : Type) where
  first : α
  second : β

/-- The smallest and largest item, or `none` for an empty list: a structure with parameters, inside an option. -/
@[export showcase_min_max]
def minMax : List Int → Option (Pair Int Int)
  | [] => none
  | x :: xs => match minMax xs with
    | none => some ⟨x, x⟩
    | some p => some ⟨min x p.first, max x p.second⟩

end Showcase
