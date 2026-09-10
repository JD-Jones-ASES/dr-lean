import DR.Endpoint.PermanentFaceStationarity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! One-sided feasible directions and the allowed positive-cofactor
comparison at a true face minimum. The positive-cofactor hypothesis is
explicit here; eliminating it needs the separate support argument. -/

namespace DittertRybin
open scoped BigOperators Topology
open Matrix Filter Set

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem PermanentFaceMinimum.direction_nonneg {allowed : ι → ι → Prop}
    {A : Matrix ι ι ℝ} (hmin : PermanentFaceMinimum allowed A)
    (B : Matrix ι ι ℝ) (hB : B ∈ doublyStochastic ℝ ι)
    (hface : ∀ i j, ¬allowed i j → B i j = 0) :
    0 ≤ ∑ i, ∑ j, (B i j-A i j)*permanentalCofactor A i j := by
  let f (t : ℝ) := Matrix.permanent (fun i j => A i j+t*(B i j-A i j))
  have hd := hasDerivAt_permanent_line A (B-A)
  change HasDerivAt f _ 0 at hd
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  have ht1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, ht1] with t ht ht1
  have hDS : (fun i j => A i j+t*(B i j-A i j)) ∈ doublyStochastic ℝ ι := by
    have h := (convex_doublyStochastic (R := ℝ) (n := ι)) hmin.1 hB
      (sub_nonneg.mpr ht1.le) ht.le (by ring : (1-t)+t = 1)
    have heq : (fun i j => A i j+t*(B i j-A i j)) = (1-t) • A+t • B := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact h
  have hf : ∀ i j, ¬allowed i j → A i j+t*(B i j-A i j) = 0 := by
    intro i j hij
    simp [hmin.2.1 i j hij, hface i j hij]
  have hm := hmin.2.2 _ hDS hf
  have hdiff : 0 ≤ f (0+t)-f 0 := by simpa [f] using sub_nonneg.mpr hm
  exact smul_nonneg (inv_nonneg.mpr ht.le) hdiff

theorem permanentalCofactor_pos_iff {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (i j : ι) :
    0 < permanentalCofactor A i j ↔
      ∃ σ : Equiv.Perm ι, σ j = i ∧ ∀ k, k ≠ j → 0 < A (σ k) k := by
  unfold permanentalCofactor
  have hn (σ : Equiv.Perm ι) : 0 ≤ if σ j = i then
      ∏ k ∈ Finset.univ.erase j, A (σ k) k else 0 := by
    split_ifs
    · exact Finset.prod_nonneg fun k _ => hA (σ k) k
    · norm_num
  rw [Finset.sum_pos_iff_of_nonneg (fun σ _ => hn σ)]
  constructor
  · rintro ⟨σ, _, hs⟩
    by_cases hij : σ j = i
    · rw [if_pos hij] at hs
      refine ⟨σ, hij, ?_⟩
      intro k hkj
      apply lt_of_le_of_ne (hA (σ k) k)
      intro hz
      have hpzero : (∏ r ∈ Finset.univ.erase j, A (σ r) r) = 0 :=
        Finset.prod_eq_zero (by simp [hkj]) hz.symm
      linarith
    · simp [hij] at hs
  · rintro ⟨σ, hij, hs⟩
    refine ⟨σ, Finset.mem_univ _, ?_⟩
    rw [if_pos hij]
    exact Finset.prod_pos fun k hk => hs k (Finset.mem_erase.mp hk).1

/-- An allowed cell with positive cofactor has the usual London comparison,
even when that cell itself is zero. -/
theorem PermanentFaceMinimum.allowed_cofactor_ge_of_pos {allowed : ι → ι → Prop}
    {A : Matrix ι ι ℝ} (hmin : PermanentFaceMinimum allowed A)
    (i j : ι) (hallowed : allowed i j) (hpos : 0 < permanentalCofactor A i j) :
    A.permanent ≤ permanentalCofactor A i j := by
  obtain ⟨σ, hσ, hmatch⟩ := (permanentalCofactor_pos_iff
    (fun _ _ => nonneg_of_mem_doublyStochastic hmin.1) i j).mp hpos
  let B : Matrix ι ι ℝ := fun r c => if r = σ c then 1 else 0
  have hB : B ∈ doublyStochastic ℝ ι := by
    apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨by intro r c; dsimp [B]; split_ifs <;> norm_num, ?_, ?_⟩
    · intro r
      have heq (c : ι) : r = σ c ↔ c = σ.symm r := by
        constructor
        · intro h; simpa using (congrArg σ.symm h).symm
        · intro h; simp [h]
      simp [B, heq]
    · intro c
      simp [B]
  have hface (r c : ι) (hnot : ¬allowed r c) : B r c = 0 := by
    dsimp [B]
    split_ifs with hrc
    · subst r
      by_cases hc : c = j
      · subst c
        exact False.elim (hnot (hσ ▸ hallowed))
      · exact False.elim ((ne_of_gt (hmatch c hc)) (hmin.2.1 (σ c) c hnot))
    · rfl
  have hdir := hmin.direction_nonneg B hB hface
  have hid : (∑ r, ∑ c, (B r c-A r c)*permanentalCofactor A r c) =
      permanentalCofactor A i j-A.permanent := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun r c => B r c*permanentalCofactor A r c)]
    have heach (c : ι) : (∑ r, B r c*permanentalCofactor A r c) =
        permanentalCofactor A (σ c) c := by simp [B, ite_mul]
    simp only [heach, permanentalCofactor_row_euler, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hval (c : ι) : permanentalCofactor A (σ c) c =
        A.permanent+(if c = j then permanentalCofactor A i j-A.permanent else 0) := by
      by_cases hc : c = j
      · simp [hc, hσ]
      · simp [hc, hmin.supported_cofactor (σ c) c (hmatch c hc)]
    simp only [hval, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hid] at hdir
  linarith

theorem PermanentFaceMinimum.allowed_cofactor_zero_or_ge {allowed : ι → ι → Prop}
    {A : Matrix ι ι ℝ} (hmin : PermanentFaceMinimum allowed A)
    (i j : ι) (hallowed : allowed i j) :
    permanentalCofactor A i j = 0 ∨ A.permanent ≤ permanentalCofactor A i j := by
  by_cases hz : permanentalCofactor A i j = 0
  · exact Or.inl hz
  · exact Or.inr (hmin.allowed_cofactor_ge_of_pos i j hallowed
      (lt_of_le_of_ne (permanentalCofactor_nonneg
        (fun _ _ => nonneg_of_mem_doublyStochastic hmin.1) i j) (Ne.symm hz)))

end
end DittertRybin
