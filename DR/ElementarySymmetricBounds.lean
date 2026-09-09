import DR.ElementarySymmetricBoundsPolynomial

/-!
# Closed-simplex elementary-symmetric bounds

The canonical elementary sums used in `DR.Rook` satisfy the normalized
Newton and Maclaurin inequalities, including vectors with zero coordinates.
Here the degree-two identity turns that comparison into marginal variance
control. No matrix extremality or rectangular endpoint claim is an assumption.
-/

namespace DittertRybin
open scoped BigOperators

private theorem multiset_esymm_two_cons (a : ℝ) (s : Multiset ℝ) :
    (a::ₘs).esymm 2 = s.esymm 2+a*s.sum := by
  simp only [Multiset.esymm,Multiset.powersetCard_cons,Multiset.powersetCard_one,
    Multiset.map_add,Multiset.sum_add,Multiset.map_map,Function.comp_def,Multiset.prod_cons,
    Multiset.prod_singleton]
  congr 1
  simpa only [Multiset.map_id'] using (Multiset.sum_map_mul_left (s := s) (f := fun x : ℝ => x) (a := a))

private theorem multiset_sum_sq_eq (s : Multiset ℝ) :
    s.sum^2 = (s.map fun x => x^2).sum+2*s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm,Multiset.powersetCard_zero_right]
  | @cons a s ih =>
    rw [Multiset.sum_cons,Multiset.map_cons,Multiset.sum_cons,multiset_esymm_two_cons]
    nlinarith

theorem elementarySymmetric_two_identity {d : ℕ} (x : Fin d → ℝ) :
    (∑ i, x i)^2 = (∑ i, x i^2)+2*elementarySymmetric x 2 := by
  have h := multiset_sum_sq_eq ((Finset.univ : Finset (Fin d)).val.map x)
  rw [Finset.esymm_map_val,← elementarySymmetric_eq_powerset_sum] at h
  simpa [Finset.sum,Multiset.map_map,Function.comp_def] using h

theorem elementarySymmetric_nonneg {d : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (k : ℕ) : 0 ≤ elementarySymmetric x k :=
  Finset.sum_nonneg fun e _ => Finset.prod_nonneg fun i _ => hx (e i)

theorem elementaryMean_nonneg {d : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (k : ℕ) : 0 ≤ elementaryMean x k :=
  div_nonneg (elementarySymmetric_nonneg hx k) (Nat.cast_nonneg _)

/-- Elementary-symmetric success relative to the uniform vector of mass one. -/
noncomputable def normalizedElementarySuccess {d : ℕ} (x : Fin d → ℝ) (k : ℕ) : ℝ :=
  (d:ℝ)^k*elementaryMean x k

/-- Squared distance of a mass-one marginal from its uniform vector. -/
noncomputable def marginalVariance {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∑ i, (x i-1/(d:ℝ))^2

theorem marginalVariance_nonneg {d : ℕ} (x : Fin d → ℝ) : 0 ≤ marginalVariance x :=
  Finset.sum_nonneg fun _i _ => sq_nonneg _

theorem marginalVariance_eq_sum_sq {d : ℕ} (hd : 0 < d)
    {x : Fin d → ℝ} (hs : ∑ i, x i = 1) :
    marginalVariance x = (∑ i, x i^2)-1/(d:ℝ) := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold marginalVariance
  simp_rw [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,← Finset.mul_sum]
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

theorem normalizedElementarySuccess_two {d : ℕ} (hd : 2 ≤ d)
    {x : Fin d → ℝ} (hs : ∑ i, x i = 1) :
    normalizedElementarySuccess x 2 = 1-(d:ℝ)/(d-1)*marginalVariance x := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (0:ℝ) < (d:ℝ)-1 := by linarith [show (2:ℝ) ≤ d by exact_mod_cast hd]
  have hc : (d.choose 2:ℝ) = (d:ℝ)*(d-1)/2 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose d 2
    norm_num [Nat.descFactorial_succ] at h
    have hh := congrArg (fun n : ℕ => (n:ℝ)) h
    push_cast [Nat.cast_sub (by omega : 1 ≤ d)] at hh
    linarith
  have he := elementarySymmetric_two_identity x
  rw [hs] at he
  rw [normalizedElementarySuccess,elementaryMean,hc,marginalVariance_eq_sum_sq (by omega) hs]
  field_simp
  nlinarith

theorem normalizedElementarySuccess_nonneg {d : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (k : ℕ) : 0 ≤ normalizedElementarySuccess x k :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (elementaryMean_nonneg hx k)

theorem normalizedElementarySuccess_maclaurin_two {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hk : 2 ≤ k) (hkd : k ≤ d) :
    normalizedElementarySuccess x k^2 ≤ normalizedElementarySuccess x 2^k := by
  have h := mul_le_mul_of_nonneg_left (elementaryMean_maclaurin_two hx hk hkd)
    (show 0 ≤ ((d:ℝ)^k)^2 from sq_nonneg _)
  simpa only [normalizedElementarySuccess,mul_pow,← pow_mul,Nat.mul_comm] using h

theorem normalizedElementarySuccess_variance_bound {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) (hk : 2 ≤ k) (hkd : k ≤ d) :
    normalizedElementarySuccess x k^2 ≤
      (1-(d:ℝ)/(d-1)*marginalVariance x)^k := by
  rw [← normalizedElementarySuccess_two (by omega) hs]
  exact normalizedElementarySuccess_maclaurin_two hx hk hkd

theorem normalizedElementarySuccess_le_one {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) (hk : 2 ≤ k) (hkd : k ≤ d) :
    normalizedElementarySuccess x k ≤ 1 := by
  have hd : 2 ≤ d := hk.trans hkd
  have hd1 : (0:ℝ) ≤ (d:ℝ)-1 := by linarith [show (2:ℝ) ≤ d by exact_mod_cast hd]
  have h2 : normalizedElementarySuccess x 2 ≤ 1 := by
    rw [normalizedElementarySuccess_two hd hs]
    exact sub_le_self _ (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hd1)
      (marginalVariance_nonneg x))
  have h := (normalizedElementarySuccess_maclaurin_two hx hk hkd).trans
    (pow_le_one₀ (normalizedElementarySuccess_nonneg hx 2) h2)
  nlinarith

end DittertRybin
