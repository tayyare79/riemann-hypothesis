module

public import Mathlib.NumberTheory.Padics.Complex

@[expose] public section

namespace Bl.general_b_fact_upper_ter_form

/-- In an algebraic closure of `ℚ_[p]`, a finite sum has norm at most `C` when every summand does and `0 ≤ C`. -/
theorem goal1 {p : Nat} [Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p)
    {C : Real} (hC : 0 ≤ C) (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

end Bl.general_b_fact_upper_ter_form
