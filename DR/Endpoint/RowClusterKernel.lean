import DR.Endpoint.RowCollisionCluster
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A quantitative retained-kernel criterion from collision clusters

A direct two-term Cauchy estimate suffices once the retained normalized row
vector has squared scaled deviation at most 1/9. It gives a 19/36 margin,
with expected collision count at most 1/12 and coefficient at least
2 m² times the retained row-product scale. No positivity of a conditional
avoidance probability is assumed.
-/

namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

/-- The scalar criterion keeps every real test vector, including constant
and zero vectors. The row vector need not be normalized for this implication. -/
theorem endpoint_cluster_scalar_gap {m : ℕ} (s x : Fin m → ℝ) (D z : ℝ)
    (hs : (∑ i,(1-(m:ℝ)*s i)^2)≤1/9)
    (hD : D≤1/12) (hz : 2*(m:ℝ)^2≤z) :
    (19/36)*(∑ i,x i^2) ≤
      z*(∑ i,s i*x i)^2+(1-3*D)*(∑ i,x i^2)-(∑ i,x i)^2 := by
  let e : Fin m → ℝ := fun i => 1-(m:ℝ)*s i
  have hsq : 0≤∑ i,x i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ e x
  have hs' : (∑ i,e i^2)≤1/9 := hs
  have he : (∑ i,e i*x i)^2≤(∑ i,x i^2)/9 := by
    have hb := mul_le_mul_of_nonneg_right hs' hsq
    nlinarith only [hc,hb]
  have hid : (∑ i,x i)=(m:ℝ)*(∑ i,s i*x i)+(∑ i,e i*x i) := by
    simp only [e,sub_mul,one_mul,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
    ring
  have hsum : (∑ i,x i)^2≤2*(m:ℝ)^2*(∑ i,s i*x i)^2+
      (2/9)*(∑ i,x i^2) := by
    rw [hid]
    nlinarith [sq_nonneg ((m:ℝ)*(∑ i,s i*x i)-(∑ i,e i*x i))]
  have hcoef := mul_le_mul_of_nonneg_right hz (sq_nonneg (∑ i,s i*x i))
  have hcol := mul_le_mul_of_nonneg_right hD hsq
  nlinarith only [hsum,hcoef,hcol]

/-- A quantitative lower bound for the actual averaging kernel, using the
actual retained row law for its collision count. -/
theorem averagingKernel_cluster_gap {m n : ℕ} (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hr : ∀ i,0<rowSum P i)
    (h : ℝ) (hh : 0<h)
    (hs : (∑ i,(1-(m:ℝ)*(rowSum P i/h))^2)≤1/9)
    (hD : rowCollisionIntensity (normalizeRows P)≤1/12)
    (hE : 2*(m:ℝ)^2*((∏ i,rowSum P i)/h^2)≤averagingCoefficient P (m-2))
    (x : Fin m → ℝ) :
    (19/36)*((∏ i,rowSum P i)/h^2)*(∑ i,x i^2)≤
      quadraticValue (averagingKernel P (m-2)) (fun i => (rowSum P i/h)*x i) := by
  let G := (∏ i,rowSum P i)/h^2
  let E := averagingCoefficient P (m-2)
  have hG : 0<G := div_pos (Finset.prod_pos (fun i _ => hr i)) (sq_pos_of_pos hh)
  have hz : 2*(m:ℝ)^2≤E/G := (le_div_iff₀ hG).mpr hE
  have hscalar := endpoint_cluster_scalar_gap (fun i => rowSum P i/h) x
    (rowCollisionIntensity (normalizeRows P)) (E/G) hs hD hz
  have hweighted := mul_le_mul_of_nonneg_left hscalar hG.le
  have hcoef : G*(E/G)=E := mul_div_cancel₀ E hG.ne'
  have hq := averagingKernel_cluster_lower P hP hr h hh x
  change E*(∑ i,(rowSum P i/h)*x i)^2+G*_
    ≤ quadraticValue (averagingKernel P (m-2)) _ at hq
  nlinarith only [hweighted,hq,congrArg
    (fun a : ℝ => a*(∑ i,(rowSum P i/h)*x i)^2) hcoef]

/-- The criterion applies to the actual kernel on all real vectors.
Positive rows provide only the invertible congruence; entries may vanish. -/
theorem averagingKernel_cluster_posDef {m n : ℕ} (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hr : ∀ i,0<rowSum P i)
    (h : ℝ) (hh : 0<h)
    (hs : (∑ i,(1-(m:ℝ)*(rowSum P i/h))^2)≤1/9)
    (hD : rowCollisionIntensity (normalizeRows P)≤1/12)
    (hE : 2*(m:ℝ)^2*((∏ i,rowSum P i)/h^2)≤averagingCoefficient P (m-2)) :
    (averagingKernel P (m-2)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    exact fun i j => averagingKernel_symmetric P (m-2) j i
  · intro x hx
    let y : Fin m → ℝ := fun i => x i/(rowSum P i/h)
    have hn (i : Fin m) : rowSum P i/h≠0 := div_ne_zero (hr i).ne' hh.ne'
    have he : (fun i => (rowSum P i/h)*y i)=x := by
      funext i
      exact mul_div_cancel₀ (x i) (hn i)
    have hy : y≠0 := by
      intro hy
      apply hx
      rw [← he]
      simp only [hy,Pi.zero_apply,mul_zero]
      rfl
    have hy2 : 0<∑ i,y i^2 := by
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hy
      exact (sq_pos_of_ne_zero hi).trans_le
        (Finset.single_le_sum (fun i _ => sq_nonneg (y i)) (Finset.mem_univ i))
    have hg := averagingKernel_cluster_gap P hP hr h hh hs hD hE y
    rw [he] at hg
    have hcoef : 0<(19/36:ℝ)*((∏ i,rowSum P i)/h^2) := mul_pos (by norm_num)
      (div_pos (Finset.prod_pos (fun i _ => hr i)) (sq_pos_of_pos hh))
    have hp := (mul_pos hcoef hy2).trans_le hg
    simpa [quadraticValue_eq_dotProduct] using hp

end DittertRybin
