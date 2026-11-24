module

public import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Order.AddGroupWithTop

@[expose] public section

namespace Bl.general_b_fact_bis

/-- Adding one on `WithBot ℕ∞` can be cancelled to recover a natural number. -/
theorem goal1 {x : WithBot ENat} {m : Nat}
    (h : x + 1 = (↑(m + 1) : WithBot ENat)) : x = (m : Nat) := by
  apply ENat.WithBot.add_one_cancel.mp
  simpa only [Nat.cast_add, Nat.cast_one] using h

end Bl.general_b_fact_bis
