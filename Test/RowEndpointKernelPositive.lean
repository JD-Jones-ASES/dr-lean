import DR.Endpoint.RowEndpointKernelPositive
import DR.ElementarySymmetricBoundsVariance

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

private noncomputable def P : Board 4 4 := Matrix.diagonal (fun _ => (1/4:ℝ))
private theorem hr (i : Fin 4) : rowSum P i=1/4 := by
  simp [P,rowSum,Matrix.diagonal_apply]
private theorem hc (j : Fin 4) : colSum P j=1/4 := by
  simp [P,colSum,Matrix.diagonal_apply]
private theorem hP : ∀ i j,0≤P i j := by
  intro i j
  by_cases hij : i=j <;> simp [P,hij]
private theorem hnorm : normalizeRows P=(1 : Board 4 4) := by
  funext i j
  simp only [normalizeRows,hr]
  by_cases hij : i=j <;> norm_num [P,Matrix.one_apply,hij]
private theorem hp : rowAvoidance (normalizeRows P)=1 := by
  rw [hnorm,rowAvoidance_square_eq_permanent]
  simp
private theorem hrow (i : Fin 4) : rowSum (normalizeRows P) i=1 := by
  rw [hnorm]
  simp [rowSum,Matrix.one_apply]
private theorem hcol (j : Fin 4) : colSum (normalizeRows P) j=1 := by
  rw [hnorm]
  simp [colSum,Matrix.one_apply]
private theorem hload (i : Fin 4) : rowCollisionLoad (normalizeRows P) i=0 := by
  rw [rowCollisionLoad_eq _ hrow]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hcol,hnorm]
  by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
private theorem ht (i : Fin 4) : rowLocalizedDoubletonLoad (normalizeRows P) i=0 := by
  have hu := rowLocalizedDoubletonLoad_le (normalizeRows P) (normalizeRows_nonneg P hP) hrow
    (fun i => by rw [hload]; norm_num) i
  rw [hload] at hu
  have hl := rowLocalizedDoubletonLoad_nonneg (normalizeRows P) (normalizeRows_nonneg P hP) i
  linarith
private theorem hv (i : Fin 4) : rowLocalizedDeficitTwoLoad (normalizeRows P) i≤0 := by
  have hu := rowLocalizedDeficitTwoLoad_le (normalizeRows P) (normalizeRows_nonneg P hP) hrow
    (fun i => by rw [hload]; norm_num) 1 (fun j => (hcol j).le) i
  simpa only [hload,zero_mul] using hu
private theorem hE : averagingCoefficient P 2=3/8 := by
  unfold averagingCoefficient
  have hcols : colSum P=(fun _ : Fin 4 => (1/4:ℝ)) := funext hc
  rw [hcols,elementarySymmetric_const]
  norm_num [Nat.choose]
private theorem hB : EndpointCollisionKernelBounds P 1 := by
  constructor
  · simp [hr]
  · simp [ht]
  · simp [ht]
  · intro i
    exact (hv i).trans (by norm_num)
  · change 4*(4:ℝ)^2≤averagingCoefficient P 2/(((∏ i,rowSum P i)/(1:ℝ)^2)*rowAvoidance (normalizeRows P))
    rw [hE,hp]
    simp_rw [hr]
    norm_num

-- This actual boundary matrix has twelve zero cells. Its exact normalized
-- row law is deterministic and injective, so all collision loads vanish.
example : (averagingKernel P 2).PosDef :=
  averagingKernel_endpoint_posDef (by decide) P hP (fun i => by rw [hr]; norm_num)
    1 (by norm_num) (by rw [hp]; norm_num) hB

-- The quantitative result handles mixed-sign vectors on the same sparse
-- matrix, with the actual gamma and avoidance factors retained.
example : (3/4096:ℝ)≤quadraticValue (averagingKernel P 2)
    (fun i => (1/4)*(![1,-1,0,0] : Fin 4 → ℝ) i) := by
  have h := averagingKernel_endpoint_gap (by decide) P hP (fun i => by rw [hr]; norm_num)
    1 (by norm_num) (by rw [hp]; norm_num) hB (![1,-1,0,0] : Fin 4 → ℝ)
  norm_num [hr,hp,Fin.sum_univ_succ] at h
  exact h

-- A zero row is not silently given a normalized probability law.
example : ¬(∀ i : Fin 4,0<rowSum (0 : Board 4 4) i) := by
  intro h
  simpa [rowSum] using h 0

#print axioms rowLocalizedDoubletonLoad_nonneg
#print axioms averagingKernel_endpoint_gap
#print axioms averagingKernel_endpoint_posDef

end DittertRybin.Tests
