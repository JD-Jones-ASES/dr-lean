import DR.Endpoint.NearEndpointMarginals
import DR.Endpoint.ConsecutiveCutGeometry
import DR.Square.SixMarginalBounds
import DR.Endpoint.MinimumDilation

/-! Size-sensitive actual cuts for n−1 iid draws on an n×n board. The
coefficient is tied to the genuine active cut and shared rook deficit;
empty/full subsets and zero deficit remain in the statements. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def nearEndpointSizedCutCoefficient (n k l : ℕ) : ℝ :=
  2*((k : ℝ)*((n : ℝ)-k)+(l : ℝ)*((n : ℝ)-l))/((k : ℝ)+l-n)^2

/-- The marginal variance estimate retains the common denominator1−a. -/
theorem nearEndpoint_marginal_variance_le {n : ℕ} (hn : 3 ≤ n)
    {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1)
    {ε : ℝ} (he0 : 0 ≤ ε) (hea : ε ≤ distinctUniformProbability n (n-1))
    (he : 1-ε ≤ normalizedElementarySuccess x (n-1)) :
    marginalVariance x ≤ 2*ε/((n : ℝ)*(1-distinctUniformProbability n (n-1))) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  have ha := distinctUniformProbability_lt_one (by omega : 0 < n) (by omega : 2 ≤ n-1)
  have he1 : ε < 1 := hea.trans_lt ha
  have hv := marginalVariance_le_of_elementary_success hx hs (by omega : 2 ≤ n-1)
    (Nat.sub_le n 1) he0 he1 he
  have hd : 0 < (n : ℝ)*((n-1 : ℕ) : ℝ)*(1-distinctUniformProbability n (n-1)) := by
    have hnk : (0 : ℝ) < ((n-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n-1)
    positivity
  apply hv.trans
  calc
    2*((n : ℝ)-1)*ε/((n : ℝ)*(n-1 : ℕ)*(1-ε)) ≤
        2*((n : ℝ)-1)*ε/((n : ℝ)*(n-1 : ℕ)*(1-distinctUniformProbability n (n-1))) :=
      div_le_div_of_nonneg_left (by positivity) hd (by gcongr)
    _ = _ := by
      rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
      field_simp

/-- A size-sensitive subset projection of the elementary deficit. -/
theorem nearEndpoint_sized_subset_sq {n : ℕ} (hn : 3 ≤ n)
    {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1)
    {ε : ℝ} (he0 : 0 ≤ ε) (hea : ε ≤ distinctUniformProbability n (n-1))
    (he : 1-ε ≤ normalizedElementarySuccess x (n-1)) (I : Finset (Fin n)) :
    ((∑ i ∈ I, x i)-I.card/(n : ℝ))^2 ≤
      (2*(I.card : ℝ)*((n : ℝ)-I.card)/(n : ℝ)^2)*ε /
        (1-distinctUniformProbability n (n-1)) := by
  have hI : (I.card : ℝ) ≤ n := by exact_mod_cast (show I.card ≤ n by simpa using I.card_le_univ)
  have hcoef : 0 ≤ (I.card : ℝ)*((n : ℝ)-I.card)/(n : ℝ) := by positivity
  have hproj := probability_subset_sq_le_card_variance (by omega : 0 < n) x hs I
  have hvar := nearEndpoint_marginal_variance_le hn hx hs he0 hea he
  apply hproj.trans ((mul_le_mul_of_nonneg_left hvar hcoef).trans_eq ?_)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have ha := distinctUniformProbability_lt_one (by omega : 0 < n) (by omega : 2 ≤ n-1)
  have hd : 1-distinctUniformProbability n (n-1) ≠ 0 := by linarith
  field_simp

/-- Both subset coefficients consume the same deficit; no row-cap premise
or product-endpoint normalization is introduced. -/
theorem nearEndpoint_contender_sized_subset_discrepancy_sq {n : ℕ} (hn : 3 ≤ n)
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (I J : Finset (Fin n)) :
    (|(∑ i ∈ I, rowSum P i)-I.card/(n : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|)^2 ≤
      (2*((I.card : ℝ)*((n : ℝ)-I.card)+(J.card : ℝ)*((n : ℝ)-J.card))/(n : ℝ)^2)*
        nearEndpointRookDeficit P/(1-distinctUniformProbability n (n-1)) := by
  obtain ⟨hdr,hdc,hbudget,_hd,hda⟩ := nearEndpoint_contender_deficit_budget hn hP hcont
  have hrow := nearEndpoint_sized_subset_sq hn (rowSum_nonneg hP.1) hP.2 hdr
    (by linarith) (by simp [nearEndpointRowRatio]) I
  have hcol := nearEndpoint_sized_subset_sq hn (colSum_nonneg hP.1)
    ((totalMass_eq_sum_colSum P).symm.trans hP.2) hdc
    (by linarith) (by simp [nearEndpointColumnRatio]) J
  have ha := distinctUniformProbability_lt_one (by omega : 0 < n) (by omega : 2 ≤ n-1)
  have hIc : (I.card : ℝ) ≤ n := by exact_mod_cast (show I.card ≤ n by simpa using I.card_le_univ)
  have hJc : (J.card : ℝ) ≤ n := by exact_mod_cast (show J.card ≤ n by simpa using J.card_le_univ)
  let A : ℝ := (2*(I.card : ℝ)*((n : ℝ)-I.card)/(n : ℝ)^2)/(1-distinctUniformProbability n (n-1))
  let B : ℝ := (2*(J.card : ℝ)*((n : ℝ)-J.card)/(n : ℝ)^2)/(1-distinctUniformProbability n (n-1))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : |(∑ i ∈ I, rowSum P i)-I.card/(n : ℝ)|^2 ≤ A*(1-nearEndpointRowRatio P) := by
    rw [sq_abs]
    exact hrow.trans_eq (by dsimp [A]; ring)
  have hc : |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|^2 ≤ B*(1-nearEndpointColumnRatio P) := by
    rw [sq_abs]
    exact hcol.trans_eq (by dsimp [B]; ring)
  have hh := add_sq_le_of_sq_le_mul hA hB hdr hdc hr hc
  apply hh.trans ((mul_le_mul_of_nonneg_left hbudget (add_nonneg hA hB)).trans_eq ?_)
  dsimp [A,B]
  ring

/-- The square cut demand has integer numerator k+l−n. -/
theorem rectangularCutDemand_square {n : ℕ} (I J : Finset (Fin n)) (hn : 0 < n) :
    rectangularCutDemand I J = ((I.card : ℝ)+J.card-n)/(n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold rectangularCutDemand
  field_simp

/-- The source coefficient multiplies the exact positive cut-demand square. -/
theorem nearEndpoint_contender_sized_cut_discrepancy_sq {n : ℕ} (hn : 3 ≤ n)
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (I J : Finset (Fin n)) (hp : 0 < rectangularCutDemand I J) :
    (|(∑ i ∈ I, rowSum P i)-I.card/(n : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|)^2 ≤
      (rectangularCutDemand I J)^2*nearEndpointSizedCutCoefficient n I.card J.card*
        nearEndpointRookDeficit P/(1-distinctUniformProbability n (n-1)) := by
  apply (nearEndpoint_contender_sized_subset_discrepancy_sq hn hP hcont I J).trans_eq
  rw [rectangularCutDemand_square I J (by omega)] at hp ⊢
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnum : (I.card : ℝ)+J.card-n ≠ 0 := ne_of_gt ((div_pos_iff_of_pos_right hn0).mp hp)
  unfold nearEndpointSizedCutCoefficient
  field_simp

/-- At any active dilation cut, the genuine scale loss is bounded by Cklδ/(1−a). -/
theorem nearEndpoint_active_dilation_loss_sq {n : ℕ} (hn : 3 ≤ n)
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    {q : ℝ} (hq1 : q ≤ 1) (I J : Finset (Fin n))
    (hp : 0 < rectangularCutDemand I J)
    (hactive : cutMass P I J = q*rectangularCutDemand I J) :
    (1-q)^2 ≤ nearEndpointSizedCutCoefficient n I.card J.card*nearEndpointRookDeficit P /
      (1-distinctUniformProbability n (n-1)) := by
  let d := |(∑ i ∈ I, rowSum P i)-I.card/(n : ℝ)|+
    |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|
  have hdev := cutMass_lower_of_subset_discrepancy hP I J (le_refl d)
  change rectangularCutDemand I J-d ≤ cutMass P I J at hdev
  rw [hactive] at hdev
  have hlow : (1-q)*rectangularCutDemand I J ≤ d := by nlinarith only [hdev]
  have hlow0 : 0 ≤ (1-q)*rectangularCutDemand I J := mul_nonneg (sub_nonneg.mpr hq1) hp.le
  have hs := pow_le_pow_left₀ hlow0 hlow 2
  have hbound := nearEndpoint_contender_sized_cut_discrepancy_sq hn hP hcont I J hp
  change d^2 ≤ _ at hbound
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hp)).mp
  convert hs.trans hbound using 1 <;> ring

/-- Actual minimum dilation and its complementary zero rectangle exist under
the weak scalar transport guards, with the sharper active-cut loss included. -/
theorem nearEndpoint_contender_exists_active_dilation {n : ℕ} (hn : 3 ≤ n)
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (ha : distinctUniformProbability n (n-1) ≤ 1/4)
    (hsize : (4/3 : ℝ)*(n : ℝ)^2*distinctUniformProbability n (n-1) < 1) :
    ∃ (q : ℝ) (B : Board n n) (I J : Finset (Fin n)),
      0 < q ∧ q ≤ 1 ∧ IsProbability B ∧
      (∀ i, rowSum B i = 1/(n : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ)) ∧
      (∀ i j, q*B i j ≤ P i j) ∧ 0 < rectangularCutDemand I J ∧
      cutMass P I J = q*rectangularCutDemand I J ∧ cutMass B Iᶜ Jᶜ = 0 ∧
      (1-q)^2 ≤ nearEndpointSizedCutCoefficient n I.card J.card*nearEndpointRookDeficit P /
        (1-distinctUniformProbability n (n-1)) := by
  obtain ⟨t,C,ht,ht1,_htsq,hC,hr,hc,hdom⟩ :=
    nearEndpoint_contender_exists_balanced_domination hn hP hcont ha hsize
  have hpositive (I J : Finset (Fin n)) (hp : 0 < rectangularCutDemand I J) :
      0 < cutMass P I J := by
    have hcut := cutMass_mono (A := (1-t) • C) (B := P) hdom I J
    rw [cutMass_smul, balanced_cut_complement_identity hC hr hc] at hcut
    have hnonneg := cutMass_nonneg hC.1 Iᶜ Jᶜ
    have hprod : 0 < (1-t)*rectangularCutDemand I J := mul_pos (sub_pos.mpr ht1) hp
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) hnonneg]
  obtain ⟨q,B,I,J,hq,hq1,hB,hrB,hcB,hdomB,hp,hactive,hzero⟩ :=
    exists_minimum_rectangular_dilation (by omega) (by omega) hP hpositive
  exact ⟨q,B,I,J,hq,hq1,hB,hrB,hcB,hdomB,hp,hactive,hzero,
    nearEndpoint_active_dilation_loss_sq hn hP hcont hq1 I J hp hactive⟩

end DittertRybin
