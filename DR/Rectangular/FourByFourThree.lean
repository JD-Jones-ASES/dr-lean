import DR.Certificates.FourByFourThree
import DR.Rectangular.OrderThreeSampling
import DR.Uniform
import Mathlib.Tactic.FinCases

/-! The exact cubic certificate acts on the original iid functional over the
entire closed 4x4 probability simplex, with quantitative stability. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

def fourByFourThreeFlat (P : Board 4 4) (u : Fin 16) : ℝ :=
  P (fourByFourThreeCell.symm u).1 (fourByFourThreeCell.symm u).2

theorem fourByFourThree_sum_flat (P : Board 4 4) :
    (∑ u,fourByFourThreeFlat P u)=totalMass P := by
  rw [← fourByFourThreeCell.sum_comp]
  simp [fourByFourThreeFlat,Fintype.sum_prod_type,totalMass,rowSum]

private def sampleThreeEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun s := (s 0,s 1,s 2)
  invFun a := ![a.1,a.2.1,a.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv a := rfl

private theorem sum_sample_three {α : Type*} [Fintype α] (f : (Fin 3 → α) → ℝ) :
    (∑ s,f s)=∑ a,∑ b,∑ c,f ![a,b,c] := by
  rw [← (sampleThreeEquiv α).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem injective_three_iff {α : Type*} (s : Fin 3 → α) :
    Function.Injective s ↔ s 0≠s 1 ∧ s 0≠s 2 ∧ s 1≠s 2 := by
  constructor
  · intro h
    exact ⟨h.ne (by decide),h.ne (by decide),h.ne (by decide)⟩
  · rintro ⟨h01,h02,h12⟩ i j h
    fin_cases i <;> fin_cases j <;> simp_all

private theorem success_flat (a b c : Fin 16) :
    RowsDistinct ![fourByFourThreeCell.symm a,fourByFourThreeCell.symm b,fourByFourThreeCell.symm c] ∨
      ColsDistinct ![fourByFourThreeCell.symm a,fourByFourThreeCell.symm b,fourByFourThreeCell.symm c] ↔
        fourByFourThreeSuccess a b c := by
  simp [RowsDistinct,ColsDistinct,injective_three_iff,fourByFourThreeSuccess,
    fourByFourThreeCell,finProdFinEquiv,Fin.ext_iff,Matrix.cons_val_two]

/-- Direct reindexing of the actual ordered iid samples, before any positivity or normalization. -/
theorem separationProbability_fourByFourThree_flat (P : Board 4 4) :
    separationProbability P 3=
      ∑ a,∑ b,∑ c,fourByFourThreeFlat P a*fourByFourThreeFlat P b*fourByFourThreeFlat P c*
        (if fourByFourThreeSuccess a b c then 1 else 0) := by
  classical
  unfold separationProbability eventMass
  rw [sum_sample_three]
  rw [← fourByFourThreeCell.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [← fourByFourThreeCell.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  rw [← fourByFourThreeCell.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Set.mem_ofPred_eq,success_flat,sampleMass,Fin.prod_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourByFourThreeFlat]
  split_ifs <;> simp

private theorem weighted_triple_certificate (p : Fin 16 → ℝ) :
    (39/64:ℝ)*(∑ a,p a)^3-
      (∑ a,∑ b,∑ c,p a*p b*p c*(if fourByFourThreeSuccess a b c then 1 else 0))=
        ∑ a,p a*quadraticValue ((fourByFourThreeMatrix a).map (fun q : ℚ => (q:ℝ))) p := by
  let f : Fin 16 → Fin 16 → Fin 16 → ℝ :=
    fun a b c => p a*p b*p c*(fourByFourThreeMatrix a b c:ℝ)
  have ht (a b c : Fin 16) : f a b c+f b a c+f c a b=
      3*(p a*p b*p c)*((39/64:ℝ)-if fourByFourThreeSuccess a b c then 1 else 0) := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (fourByFourThree_triple_identity a b c)
    push_cast at h
    by_cases hs : fourByFourThreeSuccess a b c
    all_goals
      simp only [hs,if_true,if_false,Rat.cast_one,Rat.cast_zero] at h ⊢
      dsimp [f]
      have hh := congrArg (fun z : ℝ => p a*p b*p c*z) h
      nlinarith only [hh]
  have h12 (g : Fin 16 → Fin 16 → Fin 16 → ℝ) :
      (∑ a,∑ b,∑ c,g b a c)=∑ a,∑ b,∑ c,g a b c := Finset.sum_comm
  have h23 (g : Fin 16 → Fin 16 → Fin 16 → ℝ) :
      (∑ a,∑ b,∑ c,g a c b)=∑ a,∑ b,∑ c,g a b c :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h312 : (∑ a,∑ b,∑ c,f c a b)=∑ a,∑ b,∑ c,f a b c :=
    (h23 (fun a b c => f b a c)).trans (h12 f)
  have hsum : (∑ a,∑ b,∑ c,(f a b c+f b a c+f c a b))=
      ∑ a,∑ b,∑ c,3*(p a*p b*p c)*((39/64:ℝ)-if fourByFourThreeSuccess a b c then 1 else 0) := by
    simp_rw [ht]
  simp only [Finset.sum_add_distrib] at hsum
  rw [h12 f,h312] at hsum
  have hright : (∑ a,∑ b,∑ c,3*(p a*p b*p c)*((39/64:ℝ)-if fourByFourThreeSuccess a b c then 1 else 0))=
      3*((39/64:ℝ)*(∑ a,p a)^3-
        ∑ a,∑ b,∑ c,p a*p b*p c*(if fourByFourThreeSuccess a b c then 1 else 0)) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    simp_rw [show ∀ a b c,3*(p a*p b*p c)*(39/64:ℝ)=(3*(39/64:ℝ))*(p a*p b*p c) by intros;ring,
      show ∀ a b c,3*(p a*p b*p c)*(if fourByFourThreeSuccess a b c then (1:ℝ) else 0)=
        3*(p a*p b*p c*(if fourByFourThreeSuccess a b c then (1:ℝ) else 0)) by intros;ring]
    simp only [← Finset.mul_sum,← Finset.sum_mul]
    ring
  rw [hright] at hsum
  have hf : (∑ a,∑ b,∑ c,f a b c)=
      ∑ a,p a*quadraticValue ((fourByFourThreeMatrix a).map (fun q : ℚ => (q:ℝ))) p := by
    simp only [quadraticValue,Matrix.map_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    dsimp [f]
    ring
  rw [hf] at hsum
  linarith only [hsum]

theorem fourByFourThree_homogeneous_identity (P : Board 4 4) :
    (39/64:ℝ)*totalMass P^3-separationProbability P 3=
      ∑ e,fourByFourThreeFlat P e*quadraticValue
        ((fourByFourThreeMatrix e).map (fun q : ℚ => (q:ℝ))) (fourByFourThreeFlat P) := by
  rw [separationProbability_fourByFourThree_flat,← fourByFourThree_sum_flat]
  exact weighted_triple_certificate _

/-- Literal squared Frobenius distance from the uniform 4x4 board. -/
noncomputable def fourByFourThreeEnergy (P : Board 4 4) : ℝ := ∑ i,∑ j,(P i j-1/16)^2

theorem fourByFourThree_energy_flat (P : Board 4 4) :
    (∑ e,(fourByFourThreeFlat P e-1/16)^2)=fourByFourThreeEnergy P := by
  rw [← fourByFourThreeCell.sum_comp]
  simp [fourByFourThreeFlat,Fintype.sum_prod_type,fourByFourThreeEnergy]

private theorem centered_sum_mass_one (p : Fin 16 → ℝ) (hp : ∑ i,p i=1) :
    (∑ i,p i^2)-(∑ i,p i)^2/16=∑ i,(p i-1/16)^2 := by
  have ht (i : Fin 16) : (p i-1/16)^2=p i^2-(1/8)*p i+1/256 := by ring
  simp only [ht,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    hp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Global quantitative stability on the whole closed probability simplex. -/
theorem fourByFourThree_stability {P : Board 4 4} (hP : IsProbability P) :
    (1/20:ℝ)*fourByFourThreeEnergy P≤39/64-separationProbability P 3 := by
  let p := fourByFourThreeFlat P
  have hp : ∑ i,p i=1 := (fourByFourThree_sum_flat P).trans hP.2
  have hp0 (i : Fin 16) : 0≤p i := hP.1 _ _
  have hquad (e : Fin 16) : (1/20:ℝ)*fourByFourThreeEnergy P≤
      quadraticValue ((fourByFourThreeMatrix e).map (fun q : ℚ => (q:ℝ))) p := by
    have h := fourByFourThreeMatrix_lower e p
    rw [centered_sum_mass_one p hp] at h
    exact fourByFourThree_energy_flat P ▸ h
  have hid := fourByFourThree_homogeneous_identity P
  rw [hP.2,one_pow,mul_one] at hid
  rw [hid]
  calc
    _ = ∑ e,p e*((1/20:ℝ)*fourByFourThreeEnergy P) := by
      rw [← Finset.sum_mul,hp,one_mul]
    _ ≤ _ := Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hquad e) (hp0 e)

theorem uniformMaximizer_four_by_four_three : UniformMaximizer 4 4 3 := by
  have hU : uniformSeparationValue 4 4 3=(39/64:ℝ) := by
    norm_num [uniformSeparationValue,distinctUniformProbability]
  intro P hP
  have hstab := fourByFourThree_stability hP
  have hE : 0≤fourByFourThreeEnergy P :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [hU]
  refine ⟨by linarith only [hstab,hE],?_⟩
  constructor
  · intro heq
    have hzero : fourByFourThreeEnergy P=0 := by linarith only [hstab,hE,heq]
    ext i j
    have hpart : (P i j-1/16)^2≤fourByFourThreeEnergy P := by
      apply le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (P i j-1/16)) (Finset.mem_univ j))
      exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (P i j-1/16))
        (Finset.mem_univ i)
    rw [hzero] at hpart
    have hij := sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hpart (sq_nonneg _)))
    convert hij using 1
    norm_num [uniformBoard]
  · intro heq
    rw [heq,separationProbability_uniform (by norm_num) (by norm_num),hU]

end DittertRybin
