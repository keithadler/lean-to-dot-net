## Mark what to compile

Put `@[export some_symbol]` on each Lean definition you want as a .NET method. Everything it uses is inlined.

```lean
/-- Round to cents with midpoints away from zero: the rule on an invoice. -/
@[export lean2il_finance_round_cents]
def roundCents (x : Dec) : Dec := round x 2 .awayFromZero
```

The docstring becomes the method's IntelliSense summary. Type `export` in a Lean file for a snippet.
