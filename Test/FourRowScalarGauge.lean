import DR.Rectangular.FourRowScalarGauge

namespace DittertRybin.Tests
open scoped BigOperators

-- Closed simplex and expanded quantitative target, without extremality assumptions.
example (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i) (hs : ∑ i, r i = 1) :
    29/32+(61/512)*(∑ i, (r i-1/4)^2) ≤
      (∑ i, r i*Real.sqrt (1-fourRowGaugeCollision r i))^2 :=
  fourRowScalarGauge_gap r hr hs

-- The polynomial variance constant is sharp at a simplex vertex.
example : fourRowGaugeHomogeneous ![1,0,0,0] = (183/1024:ℝ) ∧
    (61/256:ℝ)*fourRowGaugeHomogeneousVariance ![1,0,0,0] = 183/1024 := by
  simp only [fourRowGaugeHomogeneous,fourRowGaugeHomogeneousVariance]
  simp_rw [fourRowGaugeCollision_moments]
  norm_num [Fin.sum_univ_succ]

example : fourRowGaugeHomogeneous ![1,0,0,0] <
    (1/4:ℝ)*fourRowGaugeHomogeneousVariance ![1,0,0,0] := by
  simp only [fourRowGaugeHomogeneous,fourRowGaugeHomogeneousVariance]
  simp_rw [fourRowGaugeCollision_moments]
  norm_num [Fin.sum_univ_succ]

-- The all-orthant bound retains zero total mass.
example : fourRowGaugeHomogeneous (fun _ => 0) = 0 ∧
    fourRowGaugeHomogeneousVariance (fun _ => 0) = 0 := by
  simp [fourRowGaugeHomogeneous,fourRowGaugeHomogeneousVariance]

-- Uniform rows attain the scalar value; the exact equality theorem rejects all other rows.
example : (∑ i : Fin 4, (1/4:ℝ)*fourRowGaugeWeight (fun _ => 1/4) i)^2 = 29/32 :=
  (fourRowScalarGauge_eq_iff (fun _ => 1/4) (by intro i; norm_num) (by norm_num)).mpr (by intro i; rfl)

example (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i) (hs : ∑ i, r i = 1) :
    (∑ i, r i*fourRowGaugeWeight r i)^2 = 29/32 ↔ ∀ i, r i = 1/4 :=
  fourRowScalarGauge_eq_iff r hr hs

-- The square-root minorant includes x=0 and x=1/3.
example : 2*(3/32:ℝ)-2*(1/3)-(1/3-3/32)^2 ≤
    4*Real.sqrt (29/32)*(Real.sqrt (1-1/3)-Real.sqrt (29/32)) :=
  fourRowGauge_sqrt_minorant (by norm_num) (by norm_num)

#print axioms fourRowGaugeHomogeneous_permute
#print axioms fourRowScalarGaugeResidual_identity
#print axioms fourRowGaugeHomogeneous_variance_lower
#print axioms fourRowGauge_sqrt_minorant
#print axioms fourRowScalarGauge_gap
#print axioms fourRowScalarGauge_eq_iff
end DittertRybin.Tests
