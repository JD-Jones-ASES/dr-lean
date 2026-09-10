import DR.Square.Contenders
import Mathlib.Data.Nat.Choose.Sum

/-! A uniform factor-two gap for the product of two nonempty permanent
constants. Three actual terms of the binomial expansion suffice. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def gammaBinomialTerm (k l j : ℕ) : ℝ :=
  (k:ℝ)^j*(l:ℝ)^(k+l-j)*((k+l).choose j:ℝ)

theorem gammaBinomialTerm_nonneg (k l j : ℕ) : 0≤gammaBinomialTerm k l j := by
  unfold gammaBinomialTerm
  positivity

theorem gammaBinomialTerm_successor {k l : ℕ} (hl : 1≤l) :
    gammaBinomialTerm k l (k+1)*((k:ℝ)+1)=gammaBinomialTerm k l k*(k:ℝ) := by
  have hcoef := congrArg (fun v : ℕ => (v:ℝ)) (Nat.choose_succ_right_eq (k+l) k)
  have hsub : k+l-k=l := by omega
  simp only [hsub,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at hcoef
  have hpow : (l:ℝ)^l=(l:ℝ)^(l-1)*(l:ℝ) := by
    rw [← pow_succ,Nat.sub_add_cancel hl]
  unfold gammaBinomialTerm
  rw [hsub,show k+l-(k+1)=l-1 by omega,pow_succ,hpow]
  nlinarith only [congrArg (fun v : ℝ => (k:ℝ)^k*(k:ℝ)*(l:ℝ)^(l-1)*v) hcoef]

theorem gammaBinomialTerm_predecessor {k l : ℕ} (hk : 1≤k) :
    gammaBinomialTerm k l (k-1)*((l:ℝ)+1)=gammaBinomialTerm k l k*(l:ℝ) := by
  have hcoef := congrArg (fun v : ℕ => (v:ℝ)) (Nat.choose_succ_right_eq (k+l) (k-1))
  have hk' : k-1+1=k := by omega
  have hsub : k+l-(k-1)=l+1 := by omega
  simp only [hk',hsub,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at hcoef
  have hpow : (k:ℝ)^k=(k:ℝ)^(k-1)*(k:ℝ) := by
    rw [← pow_succ,Nat.sub_add_cancel hk]
  unfold gammaBinomialTerm
  rw [hsub,show k+l-k=l by omega,pow_succ,hpow]
  nlinarith only [congrArg (fun v : ℝ => (k:ℝ)^(k-1)*(l:ℝ)^l*(l:ℝ)*v) hcoef]

theorem gammaBinomialTerm_neighbors {k l : ℕ} (hk : 1≤k) (hl : 1≤l) :
    gammaBinomialTerm k l k/2≤gammaBinomialTerm k l (k-1) ∧
      gammaBinomialTerm k l k/2≤gammaBinomialTerm k l (k+1) := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hlR : (1:ℝ)≤l := by exact_mod_cast hl
  have ht := gammaBinomialTerm_nonneg k l k
  constructor
  · have hid := gammaBinomialTerm_predecessor (l:=l) hk
    have he : gammaBinomialTerm k l (k-1)=gammaBinomialTerm k l k*(l:ℝ)/((l:ℝ)+1) :=
      (eq_div_iff (by positivity)).mpr hid
    rw [he]
    apply (le_div_iff₀ (by positivity : 0<(l:ℝ)+1)).mpr
    nlinarith only [mul_nonneg ht (show 0≤(l:ℝ)-1 by linarith)]
  · have hid := gammaBinomialTerm_successor (k:=k) hl
    have he : gammaBinomialTerm k l (k+1)=gammaBinomialTerm k l k*(k:ℝ)/((k:ℝ)+1) :=
      (eq_div_iff (by positivity)).mpr hid
    rw [he]
    apply (le_div_iff₀ (by positivity : 0<(k:ℝ)+1)).mpr
    nlinarith only [mul_nonneg ht (show 0≤(k:ℝ)-1 by linarith)]

theorem gammaBinomialTerm_middle_le_half {k l : ℕ} (hk : 1≤k) (hl : 1≤l) :
    2*gammaBinomialTerm k l k≤((k:ℝ)+l)^(k+l) := by
  classical
  let S : Finset ℕ := {k-1,k,k+1}
  have hS : S⊆Finset.range (k+l+1) := by
    intro j hj
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun j _ _ => gammaBinomialTerm_nonneg k l j)
  have hSsum : (∑ j∈S,gammaBinomialTerm k l j)=
      gammaBinomialTerm k l (k-1)+gammaBinomialTerm k l k+gammaBinomialTerm k l (k+1) := by
    simp only [S,Finset.sum_insert (by simp; omega : k-1∉({k,k+1}:Finset ℕ)),
      Finset.sum_insert (by simp : k∉({k+1}:Finset ℕ)),Finset.sum_singleton]
    ring
  have htotal : (∑ j∈Finset.range (k+l+1),gammaBinomialTerm k l j)=((k:ℝ)+l)^(k+l) :=
    (add_pow (k:ℝ) (l:ℝ) (k+l)).symm
  rw [hSsum,htotal] at hsum
  have hnear := gammaBinomialTerm_neighbors hk hl
  linarith

/-- The permanent constant for every proper nonempty block decomposition
is at least twice the ambient uniform permanent constant. -/
theorem dittertConstant_mul_ge_twice {k l : ℕ} (hk : 1≤k) (hl : 1≤l) :
    2*dittertConstant (k+l)≤dittertConstant k*dittertConstant l := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hl0 : (0:ℝ)<l := by exact_mod_cast hl
  have hbin := gammaBinomialTerm_middle_le_half hk hl
  have hfac := congrArg (fun v : ℕ => (v:ℝ))
    (Nat.choose_mul_factorial_mul_factorial (show k≤k+l by omega))
  simp only [show k+l-k=l by omega,Nat.cast_mul] at hfac
  have hmul := mul_le_mul_of_nonneg_right hbin
    (by positivity : 0≤(k.factorial:ℝ)*(l.factorial:ℝ))
  unfold gammaBinomialTerm at hmul
  rw [show k+l-k=l by omega] at hmul
  have hid : 2*((k:ℝ)^k*(l:ℝ)^l*((k+l).choose k:ℝ))*
      ((k.factorial:ℝ)*(l.factorial:ℝ))=
        2*((k+l).factorial:ℝ)*(k:ℝ)^k*(l:ℝ)^l := by
    have h := congrArg (fun v : ℝ => 2*(k:ℝ)^k*(l:ℝ)^l*v) hfac
    nlinarith only [h]
  rw [hid] at hmul
  unfold dittertConstant
  rw [Nat.cast_add,div_mul_div_comm,← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity : 0<((k:ℝ)+l)^(k+l))
    (by positivity : 0<(k:ℝ)^k*(l:ℝ)^l)).mpr
  nlinarith only [hmul]

end DittertRybin
