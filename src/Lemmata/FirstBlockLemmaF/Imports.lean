module

public import Mathlib.NumberTheory.Padics.Complex

@[expose] public section

namespace Bl.FirstBlockLemmaF

/-- On `ℂ_[p]`, the norm of a difference is at most `c` when both norms are. -/
theorem goal1 (p : Nat) [hp : Fact (Nat.Prime p)] {a b : PadicComplex p} {c : Real}
    (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max a (-b)).trans (max_le ha ?_)
  rw [norm_neg]
  exact hb

end Bl.FirstBlockLemmaF
