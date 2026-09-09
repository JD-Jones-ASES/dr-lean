import DR.Rectangular.FourRowMinorantThreeFeasible
import DR.Rectangular.FourRowMinorantVariations
import Mathlib.Analysis.Convex.StdSimplex

/-! Actual compact minima on the proper probability face. A maximum squared
norm among tied minima removes nonzero flat directions without deleting a
boundary case or postulating strict curvature. -/

namespace DittertRybin
open scoped BigOperators Topology
open Filter

def IsThreeFaceMinorantMinimum (r v : Fin 4 → ℝ) : Prop :=
  ∀ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i)=1 → w 3=0 →
    fourRowMinorantHomogeneous r v ≤ fourRowMinorantHomogeneous r w

def IsThreeFaceMinorantMaxNormTie (r v : Fin 4 → ℝ) : Prop :=
  ∀ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i)=1 → w 3=0 →
    fourRowMinorantHomogeneous r w=fourRowMinorantHomogeneous r v →
    (∑ i, w i^2) ≤ ∑ i, v i^2

theorem fourRowMinorantHomogeneous_continuous_right (r : Fin 4 → ℝ) :
    Continuous (fourRowMinorantHomogeneous r) := by
  change Continuous (fun v => fourRowMinorantHomogeneous r v)
  unfold fourRowMinorantHomogeneous
  fun_prop

/-- A true minimum and a maximum norm among all equally good minima both exist. -/
theorem exists_threeFace_minorant_minimum_max_norm (r : Fin 4 → ℝ) :
    ∃ v : Fin 4 → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i,v i)=1 ∧ v 3=0 ∧
      IsThreeFaceMinorantMinimum r v ∧ IsThreeFaceMinorantMaxNormTie r v := by
  let S : Set (Fin 4 → ℝ) := stdSimplex ℝ (Fin 4) ∩ {v | v 3=0}
  have hS : IsCompact S := (isCompact_stdSimplex ℝ (Fin 4)).inter_right
    (isClosed_eq (continuous_apply 3) continuous_const)
  have hne : S.Nonempty := by
    refine ⟨![1,0,0,0],⟨⟨?_,?_⟩,rfl⟩⟩
    · intro i; fin_cases i <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three]
    · norm_num [Fin.sum_univ_succ]
  have hF := fourRowMinorantHomogeneous_continuous_right r
  obtain ⟨x,hx,hxmin⟩ := hS.exists_isMinOn hne hF.continuousOn
  let T := S ∩ {v | fourRowMinorantHomogeneous r v=fourRowMinorantHomogeneous r x}
  have hT : IsCompact T := hS.inter_right (isClosed_eq hF continuous_const)
  obtain ⟨v,hv,hvmax⟩ := hT.exists_isMaxOn ⟨x,hx,rfl⟩
    (show ContinuousOn (fun v : Fin 4 → ℝ => ∑ i,v i^2) T by fun_prop)
  refine ⟨v,hv.1.1.1,hv.1.1.2,hv.1.2,?_,?_⟩
  · intro w hw hws hw3
    rw [hv.2]
    exact hxmin ⟨⟨hw,hws⟩,hw3⟩
  · intro w hw hws hw3 heq
    exact hvmax ⟨⟨⟨hw,hws⟩,hw3⟩,heq.trans hv.2⟩

theorem threeFace_line_eventually_feasible (v w : Fin 4 → ℝ)
    (hv : ∀ i, i ≠ 3 → 0 < v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0)
    (hws : ∑ i,w i=0) (hw3 : w 3=0) :
    ∀ᶠ t : ℝ in 𝓝 0, (∀ i, 0 ≤ v i+t*w i) ∧
      (∑ i,(v i+t*w i))=1 ∧ v 3+t*w 3=0 := by
  have hp : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, i ≠ 3 → 0 < v i+t*w i := by
    rw [eventually_all]
    intro i
    by_cases hi : i=3
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hi)
    · have h := (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0).eventually_lt
        (show ContinuousAt (fun t : ℝ => v i+t*w i) 0 by fun_prop)
        (by simpa using hv i hi)
      filter_upwards [h] with t ht
      exact fun _ => ht
  filter_upwards [hp] with t ht
  refine ⟨?_,?_,by simp [hv3,hw3]⟩
  · intro i
    by_cases hi : i=3
    · simp [hi,hv3,hw3]
    · exact (ht i hi).le
  · simp only [Finset.sum_add_distrib,←Finset.mul_sum,hvs,hws,mul_zero,add_zero]

theorem IsThreeFaceMinorantMinimum.line_localMin {r v : Fin 4 → ℝ}
    (hmin : IsThreeFaceMinorantMinimum r v)
    (hv : ∀ i, i ≠ 3 → 0 < v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0)
    (w : Fin 4 → ℝ) (hws : ∑ i,w i=0) (hw3 : w 3=0) :
    IsLocalMin (fun t : ℝ => fourRowMinorantHomogeneous r (fun i => v i+t*w i)) 0 := by
  filter_upwards [threeFace_line_eventually_feasible v w hv hvs hv3 hws hw3] with t ht
  simpa only [zero_mul,add_zero] using hmin _ ht.1 ht.2.1 ht.2.2

theorem IsThreeFaceMinorantMinimum.gradient_dot_zero {r v : Fin 4 → ℝ}
    (hmin : IsThreeFaceMinorantMinimum r v)
    (hv : ∀ i, i ≠ 3 → 0 < v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0)
    (w : Fin 4 → ℝ) (hws : ∑ i,w i=0) (hw3 : w 3=0) :
    (∑ i,fourRowMinorantGradient r v i*w i)=0 := by
  have h := hmin.line_localMin hv hvs hv3 w hws hw3
  simp_rw [fourRowMinorant_line] at h
  apply fourRow_localMin_quadratic_linear_zero
  simpa only [mul_comm] using h

theorem IsThreeFaceMinorantMinimum.quadratic_nonneg {r v : Fin 4 → ℝ}
    (hmin : IsThreeFaceMinorantMinimum r v)
    (hv : ∀ i, i ≠ 3 → 0 < v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0)
    (w : Fin 4 → ℝ) (hws : ∑ i,w i=0) (hw3 : w 3=0) :
    0 ≤ fourRowMinorantQuadratic r w := by
  have h := hmin.line_localMin hv hvs hv3 w hws hw3
  simp_rw [fourRowMinorant_line] at h
  apply fourRow_localMin_quadratic_curvature_nonneg
  simpa only [mul_comm] using h

/-- At the selected actual minimum, a flat tangent direction must be zero. -/
theorem IsThreeFaceMinorantMaxNormTie.quadratic_zero {r v : Fin 4 → ℝ}
    (htie : IsThreeFaceMinorantMaxNormTie r v) (hmin : IsThreeFaceMinorantMinimum r v)
    (hv : ∀ i, i ≠ 3 → 0 < v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0)
    (w : Fin 4 → ℝ) (hws : ∑ i,w i=0) (hw3 : w 3=0)
    (hQ : fourRowMinorantQuadratic r w=0) : w=0 := by
  have hg := hmin.gradient_dot_zero hv hvs hv3 w hws hw3
  have hsame (t : ℝ) : fourRowMinorantHomogeneous r (fun i => v i+t*w i)=
      fourRowMinorantHomogeneous r v := by rw [fourRowMinorant_line,hg,hQ]; ring
  have hn : IsLocalMin (fun t : ℝ => -(∑ i,(v i+t*w i)^2)) 0 := by
    filter_upwards [threeFace_line_eventually_feasible v w hv hvs hv3 hws hw3] with t ht
    have h := htie _ ht.1 ht.2.1 ht.2.2 (hsame t)
    simpa using neg_le_neg h
  have hexp (t : ℝ) : -(∑ i,(v i+t*w i)^2)=
      -(∑ i,v i^2)+(-2*(∑ i,v i*w i))*t+(-(∑ i,w i^2))*t^2 := by
    norm_num [Fin.sum_univ_succ]
    ring
  simp_rw [hexp] at hn
  have hnorm := fourRow_localMin_quadratic_curvature_nonneg hn
  have hzero : (∑ i,w i^2)=0 := le_antisymm (by linarith)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)
  funext i
  have hwi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    sq_nonneg (w j)) (Finset.mem_univ i)
  rw [hzero] at hwi
  exact sq_eq_zero_iff.mp (le_antisymm hwi (sq_nonneg _))

end DittertRybin
