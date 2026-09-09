import DR.Square.SpectralCut
import DR.Certificates.SpectralSixGuards

/-!
# Actual matrix bounds for the order-six spectral argument

The sharper marginal estimates produce the same domination factor for all
transport cuts and all unbalanced crossing cuts. The singleton branch retains
the actual distinguished matrix entry, rather than replacing it by a common
entrywise domination factor.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates.SpectralSixGuards

/-- Every order-six contender satisfies all transport cuts for the sharper factor. -/
theorem six_contender_transportCuts (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hcont : 2 - dittertConstant 6 ≤ dittertFunctional A) :
    TransportCuts A (sixDominationFactor (sixDeficitParameter (dittertConstant 6 - A.permanent))) := by
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  obtain ⟨hrho, hsigma, hb, hd0, hdg⟩ :=
    dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hd1 := hdg.trans_lt (dittertConstant_lt_one (by norm_num))
  have ht := sixDeficitParameter_nonneg (dittertConstant 6 - A.permanent)
  have ht1 := (sixDeficitParameter_le_cap hd0 hdg).le
  have hq := sixDominationFactor_gt_two_thirds ht ht1
  intro I J
  by_cases hcard : I.card + J.card ≤ 6
  · have hcast : (I.card : ℝ) + J.card - 6 ≤ 0 := by
      have : (I.card : ℝ) + J.card ≤ 6 := by exact_mod_cast hcard
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) hcast).trans (cutMass_nonneg hA I J)
  · have hdisc := six_shared_capacity_discrepancy (rowSum A) (colSum A) hr hc hmass
      (by rwa [← totalMass_eq_sum_colSum]) (by ring) (by ring) hrho hsigma hb hd1 ht1 I J
      (by omega)
    have hlow := cutMass_ge_marginal_sum_sub_mass A hA I J
    rw [hmass] at hlow
    have hi := neg_abs_le ((∑ i ∈ I, rowSum A i) - (I.card : ℝ))
    have hj := neg_abs_le ((∑ j ∈ J, colSum A j) - (J.card : ℝ))
    norm_num only [Nat.cast_ofNat]
    nlinarith

/-- The sharper factor actually dominates a doubly stochastic matrix. -/
theorem six_contender_dominated_doublyStochastic (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hcont : 2 - dittertConstant 6 ≤ dittertFunctional A) :
    ∃ B ∈ doublyStochastic ℝ (Fin 6), ∀ i j,
      sixDominationFactor (sixDeficitParameter (dittertConstant 6 - A.permanent)) * B i j ≤ A i j := by
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hq := sixDominationFactor_gt_two_thirds
    (sixDeficitParameter_nonneg _) (sixDeficitParameter_le_cap hd0 hdg).le
  exact exists_doublyStochastic_dominated_of_cuts hA (by linarith)
    (six_contender_transportCuts A hA hmass hcont)

/-- Every unbalanced cut has actual crossing at least the sharper common factor. -/
theorem six_contender_unbalanced_crossing (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hcont : 2 - dittertConstant 6 ≤ dittertFunctional A)
    (I J : Finset (Fin 6)) (hcard : I.card ≠ J.card) :
    sixDominationFactor (sixDeficitParameter (dittertConstant 6 - A.permanent)) ≤
      cutMass A I Jᶜ + cutMass A Iᶜ J := by
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  obtain ⟨hrho, hsigma, hb, hd0, hdg⟩ :=
    dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hd1 := hdg.trans_lt (dittertConstant_lt_one (by norm_num))
  have ht := sixDeficitParameter_nonneg (dittertConstant 6 - A.permanent)
  have ht1 := (sixDeficitParameter_le_cap hd0 hdg).le
  have hq := sixDominationFactor_gt_two_thirds ht ht1
  have hdisc := six_shared_unbalanced_discrepancy (rowSum A) (colSum A) hr hc hmass
    (by rwa [← totalMass_eq_sum_colSum]) (by ring) (by ring) hrho hsigma hb hd1 ht1 I J hcard
  have hrows := cutMass_add_compl_cols A I J
  have hcols := cutMass_add_compl_rows A I J
  have hleft := cutMass_nonneg hA I Jᶜ
  have hright := cutMass_nonneg hA Iᶜ J
  have hi₁ := le_abs_self ((∑ i ∈ I, rowSum A i) - (I.card : ℝ))
  have hi₂ := neg_abs_le ((∑ i ∈ I, rowSum A i) - (I.card : ℝ))
  have hj₁ := le_abs_self ((∑ j ∈ J, colSum A j) - (J.card : ℝ))
  have hj₂ := neg_abs_le ((∑ j ∈ J, colSum A j) - (J.card : ℝ))
  rcases lt_or_gt_of_ne hcard with hlt | hgt
  · have hcast : (I.card : ℝ) + 1 ≤ J.card := by exact_mod_cast hlt
    rw [abs_of_nonpos (by linarith : (I.card : ℝ) - J.card ≤ 0)] at hdisc
    nlinarith
  · have hcast : (J.card : ℝ) + 1 ≤ I.card := by exact_mod_cast hgt
    rw [abs_of_nonneg (by linarith : 0 ≤ (I.card : ℝ) - J.card)] at hdisc
    nlinarith

/-- The exact rational quadratic used for the singleton stationarity correction. -/
theorem six_singleton_correction {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hstationary : (319 / 324 : ℝ) * u ≤ v * (1 - (643 / 324) * u)) :
    u - v ≤ 2 * (cellCorrection : ℝ) := by
  rcases hu.eq_or_lt with hu0 | hu
  · rw [← hu0]
    have hc : 0 ≤ (cellCorrection : ℝ) := by norm_num [cellCorrection]
    linarith
  have hden : 0 < 1 - (643 / 324 : ℝ) * u := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hv h
    nlinarith
  let C : ℝ := 2 * (cellCorrection : ℝ)
  have hquad : 0 < (643 / 324 : ℝ) * u ^ 2 -
      ((5 / 324) + (643 / 324) * C) * u + C := by
    have hdisc : ((5 / 324 : ℝ) + (643 / 324) * C) ^ 2 < 4 * (643 / 324) * C := by
      dsimp [C]
      norm_num [cellCorrection]
    nlinarith [sq_nonneg ((643 / 162 : ℝ) * u - ((5 / 324) + (643 / 324) * C))]
  by_contra! h
  have hmul := mul_lt_mul_of_pos_right (show v < u - C by dsimp [C]; linarith) hden
  nlinarith


/-- The actual row multiplier has the uniform lower bound `1 - gamma6`. -/
theorem six_contender_alpha_lower (A : Board 6 6) (hA : ∀ i j, 0 ≤ A i j)
    (hmass : totalMass A = 6) (hcont : 2 - dittertConstant 6 ≤ dittertFunctional A) :
    (319 / 324 : ℝ) ≤ dittertAlpha A := by
  obtain ⟨_, hC⟩ := dittert_contender_products_pos (by norm_num) A hA hmass hcont
  have hCle := colProduct_le_one (by norm_num) A hA hmass
  have hg : dittertConstant 6 = 5 / 324 := by norm_num [dittertConstant, Nat.factorial]
  rw [dittertAlpha, le_div_iff₀ hC]
  unfold dittertFunctional at hcont
  rw [hg] at hcont
  nlinarith

/-- Minimum row and maximum column marginals satisfy the improved singleton sum. -/
theorem six_globalMax_extremal_marginal_sum (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hmax : ∀ B : Board 6 6, (∀ i j, 0 ≤ B i j) → totalMass B = 6 →
      dittertFunctional B ≤ dittertFunctional A)
    (i j : Fin 6) (hmin : ∀ r, rowSum A i ≤ rowSum A r)
    (hmaxc : ∀ c, colSum A c ≤ colSum A j) :
    2 - 2 * (cellCorrection : ℝ) ≤ rowSum A i + colSum A j := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  have hri : rowSum A i ≤ 1 := by
    have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hmin r)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    change 6 * rowSum A i ≤ totalMass A at h
    rw [hmass] at h
    linarith
  have hcj : 1 ≤ colSum A j := by
    have h := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hmaxc c)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [← totalMass_eq_sum_colSum, hmass] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have ha := six_contender_alpha_lower A hA hmass hcont
  have hstationary := (dittert_globalMax_stationary_pair (by norm_num) A hA hmass hmax).1 i
  change dittertAlpha A * (rowSum A i - 1) = _ at hstationary
  have hfrac (c : Fin 6) : (colSum A c - 1) / colSum A c ≤
      (colSum A j - 1) / colSum A j := by
    apply (div_le_div_iff₀ (hc c) (hc j)).mpr
    nlinarith [hmaxc c]
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hfrac c) (hA i c))
  simp only [← Finset.sum_mul] at hsum
  have heq : (∑ c, A i c * ((colSum A c - 1) / colSum A c)) =
      ∑ c, A i c * (colSum A c - 1) / colSum A c := by
    simp only [mul_div_assoc]
  rw [heq] at hsum
  change _ ≤ rowSum A i * ((colSum A j - 1) / colSum A j) at hsum
  have hmul := mul_le_mul_of_nonneg_right ha (by linarith : 0 ≤ 1 - rowSum A i)
  have hbound : (319 / 324 : ℝ) * (1 - rowSum A i) ≤
      rowSum A i * (colSum A j - 1) / colSum A j := by
    rw [mul_div_assoc]
    nlinarith
  have hclear := (le_div_iff₀ (hc j)).mp hbound
  have hcorr := six_singleton_correction (by linarith : 0 ≤ 1 - rowSum A i)
    (by linarith : 0 ≤ colSum A j - 1)
    (by nlinarith : (319 / 324 : ℝ) * (1 - rowSum A i) ≤
      (colSum A j - 1) * (1 - (643 / 324) * (1 - rowSum A i)))
  linarith

/-- Transposition supplies the other extremal orientation produced by a
complemented sorted prefix. -/
theorem six_globalMax_extremal_marginal_sum_either (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hmax : ∀ B : Board 6 6, (∀ i j, 0 ≤ B i j) → totalMass B = 6 →
      dittertFunctional B ≤ dittertFunctional A)
    (i j : Fin 6)
    (hext : ((∀ r, rowSum A i ≤ rowSum A r) ∧ (∀ c, colSum A c ≤ colSum A j)) ∨
      ((∀ r, rowSum A r ≤ rowSum A i) ∧ (∀ c, colSum A j ≤ colSum A c))) :
    2 - 2 * (cellCorrection : ℝ) ≤ rowSum A i + colSum A j := by
  rcases hext with ⟨hmin, hmaxc⟩ | ⟨hmaxr, hminc⟩
  · exact six_globalMax_extremal_marginal_sum A hA hmass hmax i j hmin hmaxc
  · have hmassT : totalMass A.transpose = 6 := by
      change (∑ j, colSum A j) = 6
      rw [← totalMass_eq_sum_colSum, hmass]
    have hmaxT (B : Board 6 6) (hB : ∀ i j, 0 ≤ B i j) (hM : totalMass B = 6) :
        dittertFunctional B ≤ dittertFunctional A.transpose := by
      rw [dittertFunctional_transpose]
      exact hmax B hB hM
    have h := six_globalMax_extremal_marginal_sum A.transpose (fun i j => hA j i)
      hmassT hmaxT j i hminc hmaxr
    simpa only [rowSum, colSum, Matrix.transpose_apply, add_comm] using h

/-- The actual singleton cell is retained; only its crossing boundary is bounded. -/
theorem six_globalMax_singleton_cell_lower (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hmax : ∀ B : Board 6 6, (∀ i j, 0 ≤ B i j) → totalMass B = 6 →
      dittertFunctional B ≤ dittertFunctional A)
    (i j : Fin 6) (w : ℝ)
    (hext : ((∀ r, rowSum A i ≤ rowSum A r) ∧ (∀ c, colSum A c ≤ colSum A j)) ∨
      ((∀ r, rowSum A r ≤ rowSum A i) ∧ (∀ c, colSum A j ≤ colSum A c)))
    (hcross : cutMass A {i} {j}ᶜ + cutMass A {i}ᶜ {j} ≤ w) :
    1 - w / 2 - (cellCorrection : ℝ) ≤ A i j := by
  have hsum := six_globalMax_extremal_marginal_sum_either A hA hmass hmax i j hext
  have hrow := cutMass_add_compl_cols A {i} {j}
  have hcol := cutMass_add_compl_rows A {i} {j}
  simp only [cutMass, Finset.sum_singleton] at hrow hcol
  simp only [cutMass, Finset.sum_singleton] at hcross
  linarith


/-- The singleton block permanent is its actual matrix entry. -/
theorem permanent_singleton_squareCutBlock {n : ℕ} (A : Board n n) (i j : Fin n)
    (e : ({i} : Finset (Fin n)) ≃ ({j} : Finset (Fin n))) :
    (squareCutBlock A {i} {j} e).permanent = A i j := by
  have hmat : squareCutBlock A {i} {j} e = fun _ _ => A i j := by
    ext r c
    have hr : (r : Fin n) = i := Finset.mem_singleton.mp r.property
    have hc : ((e c : ({j} : Finset (Fin n))) : Fin n) = j :=
      Finset.mem_singleton.mp (e c).property
    simp [squareCutBlock, hr, hc]
  rw [hmat, permanent_const]
  simp

/-- Keep the singleton entry from `A` and dominate only its complementary
five-by-five block. This is stronger than scaling both blocks by `q`. -/
theorem permanent_lower_bound_singleton_six (A B : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hB : B ∈ doublyStochastic ℝ (Fin 6))
    (q : ℝ) (hq : 0 < q) (hdom : ∀ i j, q * B i j ≤ A i j)
    (i j : Fin 6) (w : ℝ)
    (hcross : cutMass A {i} {j}ᶜ + cutMass A {i}ᶜ {j} ≤ w) (hw : w < 2 * q) :
    A i j * dittertConstant 5 * (q - w / 2) ^ 5 ≤ A.permanent := by
  let I : Finset (Fin 6) := {i}
  let J : Finset (Fin 6) := {j}
  let e : I ≃ J := Fintype.equivOfCardEq (by simp [I, J])
  let ec : ↥(Iᶜ) ≃ ↥(Jᶜ) := Fintype.equivOfCardEq (by simp [I, J])
  let x := cutMass B I Jᶜ
  have hx0 : 0 ≤ x := cutMass_nonneg (fun i j => nonneg_of_mem_doublyStochastic hB) I Jᶜ
  have hqx : 2 * q * x ≤ w := by
    have hleft := cutMass_mono (A := fun r c => q * B r c) hdom I Jᶜ
    have hright := cutMass_mono (A := fun r c => q * B r c) hdom Iᶜ J
    have heq := doublyStochastic_opposite_cutMass_eq hB I J (by simp [I, J])
    have hs (K L : Finset (Fin 6)) : cutMass (fun r c => q * B r c) K L = q * cutMass B K L := by
      simp only [cutMass, Finset.mul_sum]
    rw [hs] at hleft hright
    rw [← heq] at hright
    change q * x ≤ _ at hleft hright
    change cutMass A I Jᶜ + cutMass A Iᶜ J ≤ w at hcross
    linarith
  have hx1 : x < 1 := by nlinarith
  have hbase : 0 ≤ q - w / 2 := by linarith
  have hcardNat : Iᶜ.card = 5 := by simp [I, Finset.card_compl]
  have hmassc : cutMass B Iᶜ Jᶜ = 5 - x := by
    have h := cutMass_add_compl_cols B Iᶜ J
    rw [← doublyStochastic_opposite_cutMass_eq hB I J (by simp [I, J])] at h
    have hrow (r) : rowSum B r = 1 := sum_row_of_mem_doublyStochastic hB r
    simp only [hrow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    have hcardc : (Iᶜ.card : ℝ) = 5 := by exact_mod_cast hcardNat
    rw [hcardc] at h
    change x + _ = _ at h
    linarith
  have hbc := squareCutBlock_substochastic hB Iᶜ Jᶜ ec
  have hperB := permanent_lower_bound_of_substochastic_fintype (squareCutBlock B Iᶜ Jᶜ ec)
    hbc.1 hbc.2.1 hbc.2.2 x hx0 hx1
    (by rw [squareCutBlock_totalMass, Fintype.card_coe, hcardNat]; exact hmassc)
  have hcard : Fintype.card ↥(Iᶜ) = 5 := by rw [Fintype.card_coe, hcardNat]
  rw [hcard] at hperB
  have hperA : dittertConstant 5 * (q - w / 2) ^ 5 ≤ (squareCutBlock A Iᶜ Jᶜ ec).permanent := by
    calc
      _ ≤ dittertConstant 5 * (q * (1 - x)) ^ 5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase (by nlinarith) 5)
          (dittertConstant_pos (by norm_num)).le
      _ = q ^ 5 * (dittertConstant 5 * (1 - x) ^ 5) := by rw [mul_pow]; ring
      _ ≤ q ^ 5 * (squareCutBlock B Iᶜ Jᶜ ec).permanent :=
        mul_le_mul_of_nonneg_left hperB (pow_nonneg hq.le 5)
      _ = (q • squareCutBlock B Iᶜ Jᶜ ec).permanent := by rw [Matrix.permanent_smul, hcard]
      _ ≤ _ := permanent_mono (fun r c => mul_nonneg hq.le (hbc.1 r c))
        (fun r c => hdom r (ec c))
  have hprod := permanent_squareCutBlocks_le A hA I J e ec
  rw [permanent_singleton_squareCutBlock] at hprod
  have h := (mul_le_mul_of_nonneg_left hperA (hA i j)).trans hprod
  simpa only [mul_assoc] using h

end DittertRybin
