import DR.Rectangular.FourRowFiniteBernstein

/-! A reusable linear form of the exact affine Bernstein transformation.
The fixed transform matrix can be checked once, avoiding a double sum at
every entry of every certificate matrix. -/

namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section

def fourRowFiniteBernsteinLinearMap {d : ℕ} (lo hi : ℚ)
    (i j : Fin (d+1)) : ℚ :=
  ∑ k : Fin (d+1), ((j : ℕ).choose k : ℚ)*lo^((j : ℕ)-k)*(hi-lo)^(k : ℕ)*
    ((i : ℕ).choose k : ℚ)/(d.choose k : ℚ)

theorem fourRowFiniteBernsteinLinearMap_apply {d : ℕ} (lo hi : ℚ)
    (p : Fin (d+1) → ℚ) (i : Fin (d+1)) :
    powerToBernstein (affinePowerCoefficients lo hi p) i =
      ∑ j, fourRowFiniteBernsteinLinearMap lo hi i j * p j := by
  unfold powerToBernstein affinePowerCoefficients fourRowFiniteBernsteinLinearMap
  simp only [Finset.sum_mul, div_eq_mul_inv]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end DittertRybin.Certificates
