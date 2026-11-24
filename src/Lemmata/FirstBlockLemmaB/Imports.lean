module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

@[expose] public section

universe u_4

namespace Bl.FirstBlockLemmaB

/-- Quotienting by a larger ideal drops Krull dimension by at least one past a prime. -/
theorem goal1 {R : Type u_4} [CommRing R] {P Q : Ideal R} [Ideal.IsPrime P]
    (hPQ : P ≤ Q) {x : R} (hxQ : x ∈ Q) (hxP : x ∉ P) :
    ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  have hne : Ideal.Quotient.mk P x ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P x)
    (mem_nonZeroDivisors_of_ne_zero hne) ?_
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact hxQ

end Bl.FirstBlockLemmaB
