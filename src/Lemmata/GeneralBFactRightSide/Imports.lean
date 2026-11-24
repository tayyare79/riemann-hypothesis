module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

namespace Bl.general_b_fact_right_side

/-- `exp (2 π i x) = 1` if and only if the real number `x` is an integer. -/
theorem goal1 (x : Real) :
    Complex.exp (2 * Complex.ofReal Real.pi * Complex.I * Complex.ofReal x) = 1 ↔
      ∃ n : Int, x = n := by
  rw [Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero,
    ← Complex.ofReal_intCast, Complex.ofReal_inj]

end Bl.general_b_fact_right_side
