import DR.Endpoint.LeadingMoments
import DR.Endpoint.RowProduct
import DR.Compactness
import Mathlib.Tactic.FunProp

/-!
# Full-simplex leading-gauge minima and zero-row exclusion

The gauge is continuous on every real board. Its compact minimum is taken
on the entire closed probability simplex. If a row vanishes, each actual
column cost equals its column mass; hence the gauge is exactly one.
-/
namespace DittertRybin
open scoped BigOperators
open Certificates

/-- A zero row forces the exact all-ones quadratic on actual nonnegative columns. -/
theorem endpointLeadingColumn_zero_row {m n : ℕ} (P : Board m n)
    (hP : ∀ i j,0≤P i j) (a : Fin m) (ha : rowSum P a=0) (j : Fin n) :
    quadraticValue (endpointLeadingKernel (rowSum P)) (fun i => P i j)=(colSum P j)^2 := by
  classical
  have haz : P a j=0 := by
    have h := Finset.single_le_sum (fun k _ => hP a k) (Finset.mem_univ j)
    change P a j≤rowSum P a at h
    rw [ha] at h
    exact le_antisymm h (hP a j)
  have he (i h : Fin m) : P i j*endpointLeadingKernel (rowSum P) i h*P h j=P i j*P h j := by
    by_cases hi : i=a
    · subst i
      simp only [haz,zero_mul]
    by_cases hh : h=a
    · subst h
      simp only [haz,mul_zero]
    by_cases hih : i=h
    · subst h
      simp [endpointLeadingKernel]
    have hm : a∈(Finset.univ.erase i).erase h := by
      simp [Ne.symm hi,Ne.symm hh]
    have hz : (∏ b∈(Finset.univ.erase i).erase h,rowSum P b)=0 :=
      Finset.prod_eq_zero hm ha
    simp [endpointLeadingKernel,hih,hz]
  unfold quadraticValue
  simp only [he,← Finset.mul_sum,← Finset.sum_mul,colSum]
  ring

theorem endpointLeadingGauge_zero_row {m n : ℕ} (P : Board m n)
    (hP : IsProbability P) (a : Fin m) (ha : rowSum P a=0) : endpointLeadingGauge P=1 := by
  have hc (j : Fin n) : endpointLeadingColumnCost P j=colSum P j := by
    unfold endpointLeadingColumnCost
    rw [endpointLeadingColumn_zero_row P hP.1 a ha]
    exact Real.sqrt_sq (colSum_nonneg hP.1 j)
  unfold endpointLeadingGauge
  simp_rw [hc]
  rw [← totalMass_eq_sum_colSum,hP.2]

/-- Positive row masses follow from an actual strict gauge bound. -/
theorem endpointLeading_rows_pos_of_lt_one {m n : ℕ} (P : Board m n)
    (hP : IsProbability P) (hG : endpointLeadingGauge P<1) : ∀ i,0<rowSum P i := by
  intro i
  by_contra hi
  have hz : rowSum P i=0 := le_antisymm (le_of_not_gt hi) (rowSum_nonneg hP.1 i)
  have hg := endpointLeadingGauge_zero_row P hP i hz
  linarith

theorem continuous_endpointLeadingGauge (m n : ℕ) :
    Continuous (endpointLeadingGauge : Board m n → ℝ) := by
  have hk (i h : Fin m) : Continuous (fun P : Board m n => endpointLeadingKernel (rowSum P) i h) := by
    by_cases hi : i=h
    · simp only [endpointLeadingKernel,hi,if_true]
      exact continuous_const
    · simp only [endpointLeadingKernel,if_neg hi]
      unfold rowSum
      fun_prop
  unfold endpointLeadingGauge endpointLeadingColumnCost quadraticValue
  apply continuous_finsetSum
  intro j hj
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro h hh
  exact ((by fun_prop : Continuous (fun P : Board m n => P i j)).mul (hk i h)).mul (by fun_prop)

/-- Actual full-board penalized minimum, rather than a minimum on a chosen support. -/
def IsEndpointGaugeMinimum {m n : ℕ} (P : Board m n) (psi : ℝ → ℝ) : Prop :=
  IsProbability P ∧ ∀ Q : Board m n, IsProbability Q →
    endpointLeadingGauge P-psi (∑ i,(rowSum P i)^2) ≤
      endpointLeadingGauge Q-psi (∑ i,(rowSum Q i)^2)

theorem exists_endpointGaugeMinimum {m n : ℕ} (hm : 0<m) (hn : 0<n)
    (psi : ℝ → ℝ) (hpsi : Continuous psi) :
    ∃ P : Board m n, IsEndpointGaugeMinimum P psi := by
  have hc : Continuous (fun P : Board m n =>
      endpointLeadingGauge P-psi (∑ i,(rowSum P i)^2)) := by
    apply (continuous_endpointLeadingGauge m n).sub
    exact hpsi.comp (by unfold rowSum; fun_prop)
  obtain ⟨P,hP,hmin⟩ := (isCompact_probabilitySimplex m n).exists_isMinOn
    ⟨uniformBoard m n,uniformBoard_isProbability hm hn⟩ hc.continuousOn
  exact ⟨P,hP,fun Q hQ => hmin hQ⟩

/-- Reconstruction uses the original row law, not a law from a deleted board. -/
theorem endpointRowBoard_normalizeRows {m n : ℕ} (P : Board m n)
    (hr : ∀ i,rowSum P i≠0) : endpointRowBoard (rowSum P) (normalizeRows P)=P := by
  ext i j
  exact mul_div_cancel₀ (P i j) (hr i)

/-- Restricting a full-simplex minimum supplies the actual row-scaling minimum. -/
theorem IsEndpointGaugeMinimum.row_minimum {m n : ℕ} {P : Board m n} {psi : ℝ → ℝ}
    (hmin : IsEndpointGaugeMinimum P psi) (hr : ∀ i,0<rowSum P i) :
    IsEndpointRowGaugeMinimum (rowSum P) (normalizeRows P) psi := by
  have hXS := normalizeRows_rowSum P (fun i => (hr i).ne')
  have hX := normalizeRows_nonneg P hmin.1.1
  have hrec := endpointRowBoard_normalizeRows P (fun i => (hr i).ne')
  intro s hs hsum
  have hQ := endpointRowBoard_isProbability s (normalizeRows P) hs hsum hX hXS
  have h := hmin.2 _ hQ
  rw [hrec]
  simpa only [rowSum_endpointRowBoard s (normalizeRows P) hXS] using h

/-- Stationarity for an actual full-board minimum, with its original row law. -/
theorem IsEndpointGaugeMinimum.stationarity {m n : ℕ} (hm : 3≤m)
    {P : Board m n} {psi : ℝ → ℝ} (hmin : IsEndpointGaugeMinimum P psi)
    (hr : ∀ i,0<rowSum P i) (tau : ℝ)
    (hpsi : HasDerivAt psi tau (∑ i,(rowSum P i)^2)) (i : Fin m) :
    endpointLeadingRowDerivative (rowSum P) (normalizeRows P) i=
      endpointLeadingGauge P-((m:ℝ)-2)*endpointLeadingMoment (rowSum P) (normalizeRows P)+
      2*tau*(rowSum P i-(∑ a,(rowSum P a)^2))+
      endpointLeadingMoment (rowSum P) (normalizeRows P)/rowSum P i := by
  have h := (hmin.row_minimum hr).stationarity hm hr hmin.1.2
    (normalizeRows_nonneg P hmin.1.1) (normalizeRows_rowSum P (fun i => (hr i).ne')) tau hpsi i
  simpa only [endpointRowBoard_normalizeRows P (fun i => (hr i).ne')] using h

end DittertRybin
