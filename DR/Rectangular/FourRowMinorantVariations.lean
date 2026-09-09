import DR.Rectangular.FourRowMinorantInterior
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual positive-simplex minimizers and the exact quadratic variation in v. -/

namespace DittertRybin
open scoped BigOperators Topology
open Filter

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def IsFourRowMinorantMinimum (r v : Fin 4 → ℝ) : Prop :=
  ∀ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
    fourRowMinorantHomogeneous r v ≤ fourRowMinorantHomogeneous r w

noncomputable def fourRowMinorantQuadratic (r w : Fin 4 → ℝ) : ℝ :=
  -2 * (∑ i, r i) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    w i*w j*∏ k ∈ (Finset.univ.erase i).erase j, r k

theorem fourRowMinorant_line (r v w : Fin 4 → ℝ) (t : ℝ) :
    fourRowMinorantHomogeneous r (fun i => v i+t*w i) =
      fourRowMinorantHomogeneous r v + t*(∑ i, fourRowMinorantGradient r v i*w i) +
        t^2*fourRowMinorantQuadratic r w := by
  norm_num [fourRowMinorantHomogeneous, fourRowMinorantGradient, fourRowMinorantQuadratic,
    fourRow_complement_product, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Finset.sum_erase, Fin.ext_iff, -Fin.val_eq_zero_iff]
  ring

/-- Strict positivity makes every mass-preserving line feasible near zero. -/
theorem IsFourRowMinorantMinimum.line_localMin {r v : Fin 4 → ℝ}
    (hmin : IsFourRowMinorantMinimum r v) (hv : ∀ i, 0 < v i) (hvs : ∑ i,v i=1)
    (w : Fin 4 → ℝ) (hws : ∑ i,w i=0) :
    IsLocalMin (fun t : ℝ => fourRowMinorantHomogeneous r (fun i => v i+t*w i)) 0 := by
  have hp : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < v i+t*w i := by
    rw [Filter.eventually_all]
    intro i
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) 0).eventually_lt
      (by fun_prop) (by simpa using hv i)
  filter_upwards [hp] with t ht
  simpa only [zero_mul, add_zero] using hmin (fun i => v i+t*w i) (fun i => (ht i).le)
    (by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hvs, hws, mul_zero, add_zero])

theorem fourRow_localMin_quadratic_linear_zero {a b c : ℝ}
    (h : IsLocalMin (fun t : ℝ => a+b*t+c*t^2) 0) : b = 0 := by
  have hd : HasDerivAt (fun t : ℝ => a+b*t+c*t^2) b 0 := by
    convert! ((hasDerivAt_const (0:ℝ) a).add ((hasDerivAt_id (0:ℝ)).const_mul b)).add
      (((hasDerivAt_id (0:ℝ)).pow 2).const_mul c) using 1
    norm_num
  exact h.hasDerivAt_eq_zero hd

theorem fourRow_localMin_quadratic_curvature_nonneg {a b c : ℝ}
    (h : IsLocalMin (fun t : ℝ => a+b*t+c*t^2) 0) : 0 ≤ c := by
  have hb := fourRow_localMin_quadratic_linear_zero h
  subst b
  have he : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ c*t^2 := by
    filter_upwards [h] with t ht
    simpa using ht
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp he
  have h := hball (show ε/2 ∈ Metric.ball (0:ℝ) ε by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith)
  exact nonneg_of_mul_nonneg_left h (sq_pos_of_pos (half_pos hε))

theorem IsFourRowMinorantMinimum.gradient_dot_zero {r v : Fin 4 → ℝ}
    (hmin : IsFourRowMinorantMinimum r v) (hv : ∀ i, 0 < v i) (hvs : ∑ i,v i=1)
    (w : Fin 4 → ℝ) (hws : ∑ i,w i=0) : ∑ i, fourRowMinorantGradient r v i*w i=0 := by
  have h := hmin.line_localMin hv hvs w hws
  simp_rw [fourRowMinorant_line] at h
  have h' : IsLocalMin (fun t : ℝ => fourRowMinorantHomogeneous r v +
      (∑ i,fourRowMinorantGradient r v i*w i)*t + fourRowMinorantQuadratic r w*t^2) 0 := by
    simpa only [mul_comm] using h
  exact fourRow_localMin_quadratic_linear_zero h'

theorem IsFourRowMinorantMinimum.quadratic_nonneg {r v : Fin 4 → ℝ}
    (hmin : IsFourRowMinorantMinimum r v) (hv : ∀ i, 0 < v i) (hvs : ∑ i,v i=1)
    (w : Fin 4 → ℝ) (hws : ∑ i,w i=0) : 0 ≤ fourRowMinorantQuadratic r w := by
  have h := hmin.line_localMin hv hvs w hws
  simp_rw [fourRowMinorant_line] at h
  have h' : IsLocalMin (fun t : ℝ => fourRowMinorantHomogeneous r v +
      (∑ i,fourRowMinorantGradient r v i*w i)*t + fourRowMinorantQuadratic r w*t^2) 0 := by
    simpa only [mul_comm] using h
  exact fourRow_localMin_quadratic_curvature_nonneg h'

noncomputable def fourRowMinorantConcentrationDirection (r : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  r i*(fourRowMinorantSquareSum r-r i)

theorem fourRowMinorantConcentrationDirection_sum (r : Fin 4 → ℝ) (hs : ∑ i,r i=1) :
    ∑ i, fourRowMinorantConcentrationDirection r i = 0 := by
  simp only [fourRowMinorantConcentrationDirection, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hs, one_mul, ← pow_two, fourRowMinorantSquareSum, sub_self]

theorem fourRowMinorantConcentrationDirection_quadratic (r : Fin 4 → ℝ) (hs : ∑ i,r i=1) :
    fourRowMinorantQuadratic r (fourRowMinorantConcentrationDirection r) =
      2*(∏ i,r i)*(4*fourRowMinorantSquareSum r-1)*fourRowMinorantDelta r := by
  have hlast : r 3 = 1-r 0-r 1-r 2 := by
    simp only [Fin.sum_univ_four] at hs
    linarith
  norm_num [fourRowMinorantQuadratic, hs, fourRowMinorantConcentrationDirection,
    fourRow_complement_product, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Finset.sum_erase, Fin.ext_iff, -Fin.val_eq_zero_iff]
  simp only [fourRowMinorantDelta, fourRowMinorantSquareSum, Fin.sum_univ_four,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl, hlast]
  ring

theorem fourRowMinorantConcentrationDirection_gradient (r v : Fin 4 → ℝ)
    (hs : ∑ i,r i=1) (hv : ∑ i,v i=1) :
    (∑ i, fourRowMinorantGradient r v i*fourRowMinorantConcentrationDirection r i) =
      fourRowMinorantDelta r * (4*(∑ i,v i*∏ j ∈ Finset.univ.erase i,r j)-fourRowMinorantE3 r) +
        (∏ i,r i)*(2-8*fourRowMinorantSquareSum r) := by
  have hlast : r 3 = 1-r 0-r 1-r 2 := by
    simp only [Fin.sum_univ_four] at hs
    linarith
  have vlast : v 3 = 1-v 0-v 1-v 2 := by
    simp only [Fin.sum_univ_four] at hv
    linarith
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  norm_num [fourRowMinorantGradient, hs, fourRowMinorantConcentrationDirection,
    fourRowGaugeCollision_moments, hs, fourRowMinorantE3_expand,
    fourRow_complement_product, Fin.sum_univ_four, Fin.prod_univ_four, hu,
    Finset.sum_erase, Finset.erase_insert, Finset.erase_insert_of_ne,
    Finset.erase_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff]
  simp only [fourRowMinorantDelta, fourRowMinorantSquareSum, Fin.sum_univ_four, hlast, vlast]
  ring

/-- An actual positive minimizer excludes both negative curvature and the singular first-order case. -/
theorem IsFourRowMinorantMinimum.squareSum_lt {r v : Fin 4 → ℝ}
    (hmin : IsFourRowMinorantMinimum r v) (hr : ∀ i, 0 < r i) (hs : ∑ i,r i=1)
    (hv : ∀ i, 0 < v i) (hvs : ∑ i,v i=1) : fourRowMinorantSquareSum r < 1/3 := by
  by_contra h
  have hq : 1/3 ≤ fourRowMinorantSquareSum r := le_of_not_gt h
  have hprod : 0 < ∏ i,r i := Finset.prod_pos (fun i _ => hr i)
  have hcurv := hmin.quadratic_nonneg hv hvs _ (fourRowMinorantConcentrationDirection_sum r hs)
  rw [fourRowMinorantConcentrationDirection_quadratic r hs] at hcurv
  have hfactor : 0 < 2*(∏ i,r i)*(4*fourRowMinorantSquareSum r-1) :=
    mul_pos (mul_pos (by norm_num) hprod) (by linarith)
  have hdelta := nonneg_of_mul_nonneg_right hcurv hfactor
  have hqeq : fourRowMinorantSquareSum r = 1/3 := by
    unfold fourRowMinorantDelta at hdelta
    linarith
  have hfirst := hmin.gradient_dot_zero hv hvs _ (fourRowMinorantConcentrationDirection_sum r hs)
  rw [fourRowMinorantConcentrationDirection_gradient r v hs hvs] at hfirst
  norm_num [fourRowMinorantDelta, hqeq] at hfirst
  linarith

end DittertRybin
