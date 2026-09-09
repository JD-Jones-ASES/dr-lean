import DR.Rectangular.OrderThreeFourRowKernel

/-! Identification of the signed row kernel with the actual iid blend, followed
by unconditional strict pair averaging for four-row contenders with N >= 960. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

private theorem totalMass_eraseRows_pair {m n : ℕ} (P : Board m n)
    (a b : Fin m) (hab : a≠b) :
    totalMass (eraseRows P {a,b})=totalMass P-rowSum P a-rowSum P b := by
  have hterm (i : Fin m) (j : Fin n) : eraseRows P {a,b} i j=P i j-
      (if i=a then P a j else 0)-(if i=b then P b j else 0) := by
    by_cases ha : i=a <;> by_cases hb : i=b <;> simp_all [eraseRows]
  simp only [totalMass,rowSum,hterm,Finset.sum_sub_distrib,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]

/-- Exact kernel identification for arbitrary signed boards, including zero total mass. -/
theorem averagingKernel_one_four_rows {n : ℕ} (P : Board 4 n) :
    averagingKernel P 1=orderThreeFourRowPairKernel (rowSum P) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [averagingKernel_one_diagonal,orderThreeFourRowPairKernel,if_true,totalMass]
  · simp only [averagingKernel,matchingExclusionKernel,if_neg hij,averagingCoefficient_one,
      rookSum_one,totalMass_eraseRows_pair P i j hij,orderThreeFourRowPairKernel]
    ring

/-- A full-simplex contender supplies the residual positive floor for every signed vector. -/
theorem orderThreeFourRow_contender_kernel_lower {n : ℕ} (hn : 960≤n)
    {P : Board 4 n} (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 3≤separationProbability P 3)
    (a b : Fin n) (hab : a≠b) (x : Fin 4 → ℝ) :
    (1/8:ℝ)*(∑ i,x i^2)≤quadraticValue (averagingKernel (eraseColumns P {a,b}) 1) x := by
  obtain ⟨hcap,hnear⟩ := orderThreeFourRow_contender_concentration hn hP hcont
  let t : Fin 4 → ℝ := fun i => P i a+P i b
  have ht : ∀ i,0≤t i := fun i => add_nonneg (hP.1 i a) (hP.1 i b)
  have htsum : (∑ i,t i)=colSum P a+colSum P b := by
    simp only [t,Finset.sum_add_distrib,colSum]
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hnreal : (960:ℝ)≤n := by exact_mod_cast hn
  have hdiv : 7/(n:ℝ)≤7/960 := by
    apply (div_le_iff₀ hnpos).mpr
    linarith only [hnreal]
  have hmass : (∑ i,t i)<1/32 := by
    rw [htsum]
    linarith only [(hcap a).trans_le hdiv,(hcap b).trans_le hdiv]
  have hlo := orderThreeFourRowPairKernel_deleted_lower (rowSum P) t x hP.2 hnear.le ht
  have hrows : rowSum (eraseColumns P {a,b})=(fun i => rowSum P i-t i) := by
    funext i
    rw [rowSum_eraseColumns_pair P a b hab]
    dsimp [t]
    ring
  rw [averagingKernel_one_four_rows,hrows]
  apply le_trans _ hlo
  have hE : 0≤∑ i,x i^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_right (by linarith only [hmass]) hE

theorem orderThreeFourRow_contender_blend_gain {n : ℕ} (hn : 960≤n)
    {P : Board 4 n} (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 3≤separationProbability P 3)
    (a b : Fin n) (hab : a≠b) :
    (3/16:ℝ)*(∑ i,(P i a-P i b)^2)≤
      separationProbability (blendColumns P a b (1/2)) 3-separationProbability P 3 := by
  have hlo := orderThreeFourRow_contender_kernel_lower hn hP hcont a b hab
    (fun i => P i a-P i b)
  have hid := separationProbability_blend_identity (k:=1) P a b hab (1/2)
  norm_num at hid
  change (1/8:ℝ)*(∑ i,(P i a-P i b)^2)≤
    ∑ i,∑ j,(P i a-P i b)*averagingKernel (eraseColumns P {a,b}) 1 i j*(P j a-P j b) at hlo
  nlinarith only [hlo,hid]

/-- Every actual global maximizer has equal columns, with no support assumption. -/
theorem IsSeparationGlobalMax.orderThreeFourRow_equal_columns {n : ℕ} {P : Board 4 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 960≤n)
    (i : Fin 4) (a b : Fin n) : P i a=P i b := by
  by_cases hab : a=b
  · subst b
    rfl
  have hcont := hmax (uniformBoard 4 n) (uniformBoard_isProbability (by norm_num) (by omega))
  have hgain := orderThreeFourRow_contender_blend_gain hn hP hcont a b hab
  have hmaxblend := hmax _ (blendColumns_isProbability hP a b hab (1/2) (by norm_num) (by norm_num))
  have hpart : (P i a-P i b)^2≤∑ j,(P j a-P j b)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (P j a-P j b)) (Finset.mem_univ i)
  have hzero : (P i a-P i b)^2=0 := by nlinarith only [hgain,hmaxblend,hpart,sq_nonneg (P i a-P i b)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)

end DittertRybin
