import DR.Rectangular.OrderThreeFourRowGauge
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp

/-! The actual four-row copositive leading bound from an exact six-square polynomial identity. -/
namespace DittertRybin
open scoped BigOperators Topology

noncomputable def orderThreeFourRowD (r v : Fin 4 → ℝ) : ℝ :=
  3*(∑ i,v i^2)-1+2*(∑ i,r i*v i)-6*(∑ i,r i*v i^2)+2*(∑ i,r i^2*v i)

noncomputable def orderThreeFourRowCofactor (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  v (i+1)*v (i+2)*v (i+3)

noncomputable def orderThreeFourRowE3 (v : Fin 4 → ℝ) : ℝ :=
  ∑ i,orderThreeFourRowCofactor v i

private noncomputable def pairSquare (v : Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  v i*v j*(v i-v j)^2*(v k+v l)^2

/-- The m=4 general symmetric numerator groups into these six nonnegative pair terms. -/
noncomputable def orderThreeFourRowSOS (v : Fin 4 → ℝ) : ℝ :=
  pairSquare v 0 1 2 3 + pairSquare v 0 2 1 3 + pairSquare v 0 3 1 2 +
  pairSquare v 1 2 0 3 + pairSquare v 1 3 0 2 + pairSquare v 2 3 0 1

theorem orderThreeFourRowSOS_nonneg (v : Fin 4 → ℝ) (hv : ∀ i,0 ≤ v i) :
    0 ≤ orderThreeFourRowSOS v := by
  have hp (i j k l : Fin 4) : 0 ≤ pairSquare v i j k l :=
    mul_nonneg (mul_nonneg (mul_nonneg (hv i) (hv j)) (sq_nonneg _)) (sq_nonneg _)
  unfold orderThreeFourRowSOS
  repeat' apply add_nonneg
  all_goals apply hp

/-- A division-free completion of squares, with the exact symmetric numerator.
The identity holds for signed row and column vectors of total mass one. -/
theorem orderThreeFourRowD_completion (r v : Fin 4 → ℝ)
    (hr : ∑ i,r i=1) (hv : ∑ i,v i=1) :
    2*orderThreeFourRowE3 v^2*orderThreeFourRowD r v =
      (∑ i,v i*(2*orderThreeFourRowE3 v*r i-orderThreeFourRowE3 v*(3*v i-1)-
        3*orderThreeFourRowCofactor v i)^2)+3*orderThreeFourRowE3 v*orderThreeFourRowSOS v := by
  have hr3 : r 3=1-r 0-r 1-r 2 := by rw [Fin.sum_univ_four] at hr; linarith only [hr]
  have hv3 : v 3=1-v 0-v 1-v 2 := by rw [Fin.sum_univ_four] at hv; linarith only [hv]
  simp only [orderThreeFourRowD,orderThreeFourRowE3,orderThreeFourRowCofactor,
    orderThreeFourRowSOS,pairSquare,Fin.sum_univ_four,Fin.reduceAdd]
  rw [hr3,hv3]
  ring

/-- Positivity on the relative interior follows from the exact polynomial certificate. -/
theorem orderThreeFourRowD_nonneg_of_positive (r v : Fin 4 → ℝ)
    (hr : ∑ i,r i=1) (hv : ∑ i,v i=1) (hvpos : ∀ i,0<v i) :
    0 ≤ orderThreeFourRowD r v := by
  have he : 0 < orderThreeFourRowE3 v :=
    Finset.sum_pos (fun i _ => mul_pos (mul_pos (hvpos (i+1)) (hvpos (i+2))) (hvpos (i+3)))
      Finset.univ_nonempty
  have hs : 0 ≤ ∑ i,v i*(2*orderThreeFourRowE3 v*r i-orderThreeFourRowE3 v*(3*v i-1)-
      3*orderThreeFourRowCofactor v i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (hvpos i).le (sq_nonneg _)
  have hp := orderThreeFourRowSOS_nonneg v (fun i => (hvpos i).le)
  have hid := orderThreeFourRowD_completion r v hr hv
  have hnum : 0 ≤ 2*orderThreeFourRowE3 v^2*orderThreeFourRowD r v := by
    rw [hid]
    exact add_nonneg hs (mul_nonneg (by positivity) hp)
  exact nonneg_of_mul_nonneg_right hnum (by positivity)

/-- Polynomial continuity retains all boundary column vectors, including support of size one or two. -/
theorem orderThreeFourRowD_nonneg (r v : Fin 4 → ℝ)
    (hr : ∑ i,r i=1) (hv : ∑ i,v i=1) (hv0 : ∀ i,0≤v i) :
    0 ≤ orderThreeFourRowD r v := by
  let f (t : ℝ) := orderThreeFourRowD r (fun i => (v i+t)/(1+4*t))
  have hc : ContinuousAt f 0 := by
    unfold f orderThreeFourRowD
    fun_prop (disch := norm_num)
  have hl : Filter.Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (orderThreeFourRowD r v)) := by
    simpa only [f,add_zero,mul_zero,div_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0<t := ht
  have hden : 0<1+4*t := by positivity
  apply orderThreeFourRowD_nonneg_of_positive r _ hr
  · simp only [← Finset.sum_div,Finset.sum_add_distrib,hv,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact div_self (ne_of_gt hden)
  · intro i
    exact div_pos (add_pos_of_nonneg_of_pos (hv0 i) ht0) hden

/-- The normalized leading column quadratic, before the factor three in the failure polynomial. -/
noncomputable def orderThreeFourRowQuadratic (r v : Fin 4 → ℝ) : ℝ :=
  (∑ i,v i^2)+2*(∑ i,v i)*(∑ i,r i*v i)-2*(∑ i,r i*v i^2)

private theorem weighted_square_le (v f : Fin 4 → ℝ) (hv0 : ∀ i,0≤v i) (hv : ∑ i,v i=1) :
    (∑ i,v i*f i)^2 ≤ ∑ i,v i*f i^2 := by
  have hs : 0≤∑ i,v i*(f i-(∑ j,v j*f j))^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hv0 i) (sq_nonneg _)
  simp only [sub_sq,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,hv] at hs
  have hc : (∑ i,v i*(2*f i*(∑ j,v j*f j)))=2*(∑ i,v i*f i)^2 := by
    calc
      _ = (∑ i,v i*f i)*(2*(∑ j,v j*f j)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by ring
  rw [hc] at hs
  nlinarith only [hs]

/-- The actual rank-one minorant on the closed column probability simplex. -/
theorem orderThreeFourRowQuadratic_probability_lower (r v : Fin 4 → ℝ)
    (hr0 : ∀ i,0≤r i) (hr : ∑ i,r i=1) (hv0 : ∀ i,0≤v i) (hv : ∑ i,v i=1) :
    (∑ i,v i*orderThreeFourRowWeight (r i))^2 ≤ orderThreeFourRowQuadratic r v := by
  have hri (i : Fin 4) : r i≤1 := by
    calc
      _ ≤ ∑ j,r j := Finset.single_le_sum (fun j _ => hr0 j) (Finset.mem_univ i)
      _ = 1 := hr
  have hw (i : Fin 4) : orderThreeFourRowWeight (r i)^2=1-(2/3)*(1-r i)^2 := by
    apply Real.sq_sqrt
    nlinarith [mul_nonneg (hr0 i) (sub_nonneg.mpr (hri i))]
  have hD := orderThreeFourRowD_nonneg r v hr hv hv0
  have hid : orderThreeFourRowQuadratic r v-(∑ i,v i*orderThreeFourRowWeight (r i)^2) =
      orderThreeFourRowD r v/3 := by
    have hv3 : v 3=1-v 0-v 1-v 2 := by rw [Fin.sum_univ_four] at hv; linarith only [hv]
    simp only [hw,orderThreeFourRowQuadratic,orderThreeFourRowD,Fin.sum_univ_four,hv3]
    ring
  have hcs := weighted_square_le v (fun i => orderThreeFourRowWeight (r i)) hv0 hv
  linarith only [hD,hid,hcs]

/-- Scaling is literal polynomial homogeneity; it permits signed scalars and vectors. -/
theorem orderThreeFourRowQuadratic_smul (r v : Fin 4 → ℝ) (t : ℝ) :
    orderThreeFourRowQuadratic r (fun i => t*v i)=t^2*orderThreeFourRowQuadratic r v := by
  simp only [orderThreeFourRowQuadratic,Fin.sum_univ_four]
  ring

/-- The leading rank-one bound is copositive and holds for every nonnegative column,
including the zero vector. It is not asserted for arbitrary signed columns. -/
theorem orderThreeFourRowQuadratic_lower (r v : Fin 4 → ℝ)
    (hr0 : ∀ i,0≤r i) (hr : ∑ i,r i=1) (hv0 : ∀ i,0≤v i) :
    (∑ i,v i*orderThreeFourRowWeight (r i))^2 ≤ orderThreeFourRowQuadratic r v := by
  let s := ∑ i,v i
  have hs0 : 0≤s := Finset.sum_nonneg fun i _ => hv0 i
  by_cases hs : s=0
  · have hzero (i : Fin 4) : v i=0 := by
      have hi := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hv0 j) (Finset.mem_univ i)
      change v i≤s at hi
      exact le_antisymm (hi.trans_eq hs) (hv0 i)
    simp [hzero,orderThreeFourRowQuadratic]
  have hspos : 0<s := lt_of_le_of_ne hs0 (Ne.symm hs)
  let u (i : Fin 4) := s⁻¹*v i
  have hu0 (i : Fin 4) : 0≤u i := mul_nonneg (inv_nonneg.mpr hs0) (hv0 i)
  have hu : ∑ i,u i=1 := by
    simp only [u,← Finset.mul_sum]
    exact inv_mul_cancel₀ hs
  have h := orderThreeFourRowQuadratic_probability_lower r u hr0 hr hu0 hu
  rw [orderThreeFourRowQuadratic_smul] at h
  have hlin : (∑ i,u i*orderThreeFourRowWeight (r i)) = s⁻¹*(∑ i,v i*orderThreeFourRowWeight (r i)) := by
    simp only [u,mul_assoc,Finset.mul_sum]
  rw [hlin,mul_pow] at h
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (inv_pos.mpr hspos))).mp h

end DittertRybin
