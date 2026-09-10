import DR.Endpoint.LeadingKernel
import Mathlib.Analysis.MeanInequalities

/-!
# Closed-simplex bounds for actual leading column costs

AM--GM controls every complementary product. The sharper diagonal term
retains the factor `1 - 1/m` in the cost defect; this is the input needed
for the general endpoint gauge minimum, not a PSD assertion on all vectors.
-/
namespace DittertRybin
open scoped BigOperators
open Certificates

noncomputable def endpointLeadingDefect (m : ℕ) : ℝ :=
  dittertConstant (m-2)*(1-1/(m:ℝ))

/-- Finite-set AM--GM with a natural power, including zero coordinates. -/
theorem endpoint_finset_prod_le_mean_pow {ι : Type*} (S : Finset ι)
    (z : ι → ℝ) (hS : 0<S.card) (hz : ∀ i∈S,0≤z i) :
    (∏ i∈S,z i)≤((∑ i∈S,z i)/(S.card:ℝ))^S.card := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast hS.ne'
  have hw : (∑ _i∈S,(S.card:ℝ)⁻¹)=1 := by simp [hn]
  have hg := Real.geom_mean_le_arith_mean_weighted S (fun _ => (S.card:ℝ)⁻¹) z
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hw hz
  have hp := pow_le_pow_left₀
    (Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (hz i hi) _)) hg S.card
  rw [← Finset.prod_pow] at hp
  have he : (∏ i∈S,(z i^((S.card:ℝ)⁻¹))^S.card)=∏ i∈S,z i := by
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.rpow_inv_natCast_pow (hz i hi) hS.ne'
  rw [he] at hp
  rw [← Finset.mul_sum] at hp
  simpa only [div_eq_mul_inv,mul_comm] using hp

/-- Every complementary-product entry obeys the sharp AM--GM cap. -/
theorem endpointLeading_complement_bounds {m : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (i j : Fin m) (hij : i≠j) :
    0≤((m-2).factorial:ℝ)*(∏ a∈(Finset.univ.erase i).erase j,r a) ∧
    ((m-2).factorial:ℝ)*(∏ a∈(Finset.univ.erase i).erase j,r a)≤dittertConstant (m-2) := by
  classical
  let S := (Finset.univ.erase i).erase j
  have hc : S.card=m-2 := by
    rw [Finset.card_erase_of_mem (show j∈Finset.univ.erase i by simp [Ne.symm hij]),
      Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
    omega
  have hsum : (∑ a∈S,r a)≤1 := by
    calc
      _ ≤ ∑ a,r a := Finset.sum_le_univ_sum_of_nonneg hr
      _ = 1 := hs
  have hk : 0<(m-2:ℕ) := by omega
  have hkR : (0:ℝ)<(m-2:ℕ) := by exact_mod_cast hk
  have hp := endpoint_finset_prod_le_mean_pow S r (by omega) (fun a _ => hr a)
  rw [hc] at hp
  have hb := pow_le_pow_left₀
    (div_nonneg (Finset.sum_nonneg (fun a _ => hr a)) hkR.le)
    (div_le_div_of_nonneg_right hsum hkR.le) (m-2)
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun a _ => hr a)), ?_⟩
  have h := mul_le_mul_of_nonneg_left (hp.trans hb) (Nat.cast_nonneg (m-2).factorial : (0:ℝ)≤_)
  simpa only [dittertConstant,div_pow,one_pow,mul_one_div] using h

/-- The cost bound is restricted to nonnegative column vectors. The
leading kernel need not be positive semidefinite at arbitrary marginals. -/
theorem endpointLeadingKernel_quadratic_bounds {m : ℕ} (hm : 3≤m)
    (r v : Fin m → ℝ) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hv : ∀ i,0≤v i) :
    (1-endpointLeadingDefect m)*(∑ i,v i)^2 ≤ quadraticValue (endpointLeadingKernel r) v ∧
      quadraticValue (endpointLeadingKernel r) v ≤ (∑ i,v i)^2 := by
  classical
  let a := dittertConstant (m-2)
  have ha : 0≤a := div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have he (i j : Fin m) :
      1-a+(if i=j then a else 0)≤endpointLeadingKernel r i j ∧
        endpointLeadingKernel r i j≤1 := by
    by_cases hij : i=j
    · subst j
      simp [endpointLeadingKernel]
    · have h := endpointLeading_complement_bounds hm r hr hs i j hij
      simp only [endpointLeadingKernel,if_neg hij,add_zero]
      exact ⟨by linarith,by linarith⟩
  have hlo := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (he i j).1 (hv i)) (hv j)))
  have hhi := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (he i j).2 (hv i)) (hv j)))
  have hid : (∑ i,∑ j,v i*(1-a+(if i=j then a else 0))*v j)=
      (1-a)*(∑ i,v i)^2+a*(∑ i,v i^2) := by
    simp only [mul_add,add_mul,Finset.sum_add_distrib,mul_ite,ite_mul,mul_zero,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,if_true]
    have hd : (∑ i,v i*a*v i)=a*∑ i,v i^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hd]
    simp only [← Finset.mul_sum,← Finset.sum_mul]
    ring
  rw [hid] at hlo
  change _≤quadraticValue (endpointLeadingKernel r) v at hlo
  have hupper : quadraticValue (endpointLeadingKernel r) v≤(∑ i,v i)^2 := by
    simp only [mul_one] at hhi
    have hc : (∑ i,∑ j,v i*v j)=(∑ i,v i)^2 := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      ring
    rw [hc] at hhi
    exact hhi
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1:ℝ)) v
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at hcs
  have hmR : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hvar : (∑ i,v i)^2/(m:ℝ)≤∑ i,v i^2 := (div_le_iff₀ hmR).mpr (by simpa only [mul_comm] using hcs)
  have hmul := mul_le_mul_of_nonneg_left hvar ha
  have heq : (1-endpointLeadingDefect m)*(∑ i,v i)^2=
      (1-a)*(∑ i,v i)^2+a*((∑ i,v i)^2/(m:ℝ)) := by
    unfold endpointLeadingDefect
    dsimp [a]
    ring
  exact ⟨by rw [heq]; linarith,hupper⟩

/-- The elementary factorial cap is enough for strict positivity of each
nonzero nonnegative column; no gauge minimum is assumed here. -/
theorem endpointLeadingDefect_bounds {m : ℕ} (hm : 3≤m) :
    0≤endpointLeadingDefect m ∧ endpointLeadingDefect m<1 := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
  have hm0 : (0:ℝ)<m := by linarith
  have hk : 0<(m-2:ℕ) := by omega
  have hkR : (0:ℝ)<(m-2:ℕ) := by exact_mod_cast hk
  have ha0 : 0≤dittertConstant (m-2) := by unfold dittertConstant; positivity
  have ha1 : dittertConstant (m-2)≤1 := by
    unfold dittertConstant
    apply (div_le_one (pow_pos hkR _)).mpr
    exact_mod_cast Nat.factorial_le_pow (m-2)
  have hi : 1/(m:ℝ)≤1 := (div_le_one hm0).mpr hmR
  have hp : 0<1/(m:ℝ) := one_div_pos.mpr hm0
  unfold endpointLeadingDefect
  constructor
  · exact mul_nonneg ha0 (by linarith)
  · have h := mul_le_mul_of_nonneg_right ha1 (show 0≤1-1/(m:ℝ) by linarith)
    nlinarith

theorem endpointLeadingColumnCost_bounds {m n : ℕ} (hm : 3≤m)
    (P : Board m n) (hP : IsProbability P) (j : Fin n) :
    Real.sqrt (1-endpointLeadingDefect m)*colSum P j≤endpointLeadingColumnCost P j ∧
      endpointLeadingColumnCost P j≤colSum P j := by
  have hr : ∀ i,0≤rowSum P i := fun i => Finset.sum_nonneg (fun j _ => hP.1 i j)
  have hc : 0≤colSum P j := Finset.sum_nonneg (fun i _ => hP.1 i j)
  have h := endpointLeadingKernel_quadratic_bounds hm (rowSum P) (fun i => P i j)
    hr hP.2 (fun i => hP.1 i j)
  have hb : 0≤1-endpointLeadingDefect m := by linarith [(endpointLeadingDefect_bounds hm).2]
  constructor
  · unfold endpointLeadingColumnCost colSum
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow,Real.sq_sqrt hb]
    exact h.1
  · unfold endpointLeadingColumnCost
    exact (Real.sqrt_le_left hc).mpr h.2

theorem endpointLeadingColumnCost_pos {m n : ℕ} (hm : 3≤m)
    (P : Board m n) (hP : IsProbability P) (j : Fin n) (hc : 0<colSum P j) :
    0<endpointLeadingColumnCost P j := by
  have hb : 0<1-endpointLeadingDefect m := by linarith [(endpointLeadingDefect_bounds hm).2]
  exact (mul_pos (Real.sqrt_pos.mpr hb) hc).trans_le (endpointLeadingColumnCost_bounds hm P hP j).1

theorem endpointLeadingColumnCost_eq_zero_iff {m n : ℕ} (hm : 3≤m)
    (P : Board m n) (hP : IsProbability P) (j : Fin n) :
    endpointLeadingColumnCost P j=0 ↔ colSum P j=0 := by
  constructor
  · intro h
    by_contra hc
    have hp : 0<colSum P j := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => hP.1 i j)) (Ne.symm hc)
    have hh := endpointLeadingColumnCost_pos hm P hP j hp
    linarith
  · intro hc
    have h := (endpointLeadingColumnCost_bounds hm P hP j).2
    have h0 := Real.sqrt_nonneg (quadraticValue (endpointLeadingKernel (rowSum P)) (fun i => P i j))
    change 0≤endpointLeadingColumnCost P j at h0
    linarith

end DittertRybin
