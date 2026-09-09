import DR.Rectangular.FourRowMinorantThreeFace
import DR.Rectangular.FourRowMinorantRowCurve

/-! The actual closed fixed-q stationary-feasibility set and its compact
objective maximum. The denominator is constant on this set, so continuity
does not make an implicit assertion across the singular q=1/3 level. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowMinorantFixedStationary (q : ℝ) (r : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  1/4+r i*(q-r i)/(2*(1-3*q))

def fourRowMinorantFixedFeasible (q : ℝ) : Set (Fin 4 → ℝ) :=
  stdSimplex ℝ (Fin 4) ∩ {r | fourRowMinorantSquareSum r=q} ∩
    {r | ∀ i,0≤fourRowMinorantFixedStationary q r i}

theorem fourRowMinorantFixedStationary_eq (q : ℝ) (r : Fin 4 → ℝ)
    (hq : fourRowMinorantSquareSum r=q) :
    fourRowMinorantFixedStationary q r=fourRowMinorantStationary r := by
  funext i
  simp only [fourRowMinorantFixedStationary,fourRowMinorantStationary,fourRowMinorantDelta,hq]

theorem fourRowMinorantFixedFeasible_isCompact (q : ℝ) :
    IsCompact (fourRowMinorantFixedFeasible q) := by
  have hQ : Continuous fourRowMinorantSquareSum := by
    unfold fourRowMinorantSquareSum
    fun_prop
  have hc : IsClosed {r : Fin 4 → ℝ | ∀ i,0≤fourRowMinorantFixedStationary q r i} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_le continuous_const
    unfold fourRowMinorantFixedStationary
    fun_prop
  exact ((isCompact_stdSimplex ℝ (Fin 4)).inter_right (isClosed_eq hQ continuous_const)).inter_right hc

theorem exists_fourRowMinorant_fixed_maximum (γ : ℝ) (r : Fin 4 → ℝ)
    (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1) (hv : ∀ i,0≤fourRowMinorantStationary r i) :
    ∃ u : Fin 4 → ℝ, (∀ i,0≤u i) ∧ (∑ i,u i)=1 ∧
      fourRowMinorantSquareSum u=fourRowMinorantSquareSum r ∧
      (∀ i,0≤fourRowMinorantStationary u i) ∧ IsFourRowMinorantRowMaximum γ u ∧
      fourRowMinorantRowObjective γ r ≤ fourRowMinorantRowObjective γ u := by
  let q := fourRowMinorantSquareSum r
  have hin : r ∈ fourRowMinorantFixedFeasible q := by
    refine ⟨⟨⟨hr,hs⟩,rfl⟩,?_⟩
    change ∀ i,0≤fourRowMinorantFixedStationary q r i
    rw [fourRowMinorantFixedStationary_eq q r rfl]
    exact hv
  have hcont : Continuous (fourRowMinorantRowObjective γ) := by
    change Continuous (fun u => fourRowMinorantRowObjective γ u)
    unfold fourRowMinorantRowObjective fourRowMinorantE3
    fun_prop
  obtain ⟨u,hu,hmax⟩ := (fourRowMinorantFixedFeasible_isCompact q).exists_isMaxOn
    ⟨r,hin⟩ hcont.continuousOn
  refine ⟨u,hu.1.1.1,hu.1.1.2,hu.1.2,?_,?_,hmax hin⟩
  · have hfix := hu.2
    change ∀ i,0≤fourRowMinorantFixedStationary q u i at hfix
    simpa only [fourRowMinorantFixedStationary_eq q u hu.1.2] using hfix
  · intro w hw hws hwq hwv
    apply hmax
    have hQ : fourRowMinorantSquareSum w=q := hwq.trans hu.1.2
    refine ⟨⟨⟨hw,hws⟩,hQ⟩,?_⟩
    change ∀ i,0≤fourRowMinorantFixedStationary q w i
    simpa only [fourRowMinorantFixedStationary_eq q w hQ] using hwv

theorem fourRowMinorantSquareSum_ge_quarter (r : Fin 4 → ℝ) (hs : ∑ i,r i=1) :
    1/4 ≤ fourRowMinorantSquareSum r := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r (fun _ => (1 : ℝ))
  simp only [mul_one,hs,one_pow,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at h
  change (1 : ℝ) ≤ fourRowMinorantSquareSum r*4 at h
  linarith

theorem fourRowMinorant_rows_eq_quarter (r : Fin 4 → ℝ) (hs : ∑ i,r i=1)
    (hq : fourRowMinorantSquareSum r=1/4) : r=fun _ => 1/4 := by
  have hid : (∑ i,(r i-1/4)^2)=fourRowMinorantSquareSum r-1/4 := by
    simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [←Finset.sum_mul,←Finset.mul_sum,hs]
    unfold fourRowMinorantSquareSum
    ring
  have hz : (∑ i,(r i-1/4)^2)=0 := by rw [hid,hq,sub_self]
  funext i
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    sq_nonneg (r j-1/4)) (Finset.mem_univ i)
  rw [hz] at hi
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _)))

theorem fourRowMinorant_rows_pos_of_squareSum_lt (r : Fin 4 → ℝ)
    (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1) (hq : fourRowMinorantSquareSum r<1/3) :
    ∀ i,0<r i := by
  intro i
  by_contra h
  have hz : r i=0 := le_antisymm (le_of_not_gt h) (hr i)
  have hs' := Finset.sum_erase_add Finset.univ r (Finset.mem_univ i)
  have hq' := Finset.sum_erase_add Finset.univ (fun j => r j^2) (Finset.mem_univ i)
  rw [hz,add_zero,hs] at hs'
  simp only [hz,zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero] at hq'
  have hC := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i) r (fun _ => (1 : ℝ))
  simp only [mul_one,hs',one_pow,Finset.sum_const,nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin] at hC
  rw [hq'] at hC
  change (1 : ℝ) ≤ fourRowMinorantSquareSum r*(4-1 : ℕ) at hC
  norm_num at hC
  linarith

end DittertRybin
