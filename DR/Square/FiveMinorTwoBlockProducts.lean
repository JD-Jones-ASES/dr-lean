import DR.Square.FiveMinorGeometry
import DR.Square.FiveMinorFactors

/-! The four product factors are derived from the actual ordered two-by-two cut. -/

namespace DittertRybin
open scoped BigOperators

theorem five_two_block_actual_products (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (I J : Finset (Fin 5)) (hI : I.card = 2) (hJ : J.card = 2)
    (horder : LowerMarginalCut A I J)
    (hrL : ∀ i, 79/100 ≤ rowSum A i) (hcL : ∀ j, 79/100 ≤ colSum A j)
    (u v w : ℝ) (hrI : (∑ i ∈ I, rowSum A i) = 2-u)
    (hcJ : (∑ j ∈ J, colSum A j) = 2+v)
    (hw : cutMass A I Jᶜ + cutMass A Iᶜ J = w) (hw1 : w ≤ 13/50) :
    ((∏ i, rowSum A i) * fiveSmallRowFactor u v w ≤ ∏ i : I, ∑ j ∈ J, A i j) ∧
    ((∏ j, colSum A j) * fiveSmallColFactor u v w ≤ ∏ j : J, ∑ i ∈ I, A i j) ∧
    ((∏ i, rowSum A i) * fiveLargeRowFactor u v w ≤ ∏ i : ↥(Iᶜ), ∑ j ∈ Jᶜ, A i j) ∧
    ((∏ j, colSum A j) * fiveLargeColFactor u v w ≤ ∏ j : ↥(Jᶜ), ∑ i ∈ Iᶜ, A i j) := by
  obtain ⟨hu,hv⟩ := lower_cut_defects_nonneg (by norm_num) A I J horder hmass 2 hI hJ u v hrI hcJ
  have huw := crossing_ge_defect_sum A hA I J 2 u v w 5 hmass hrI hcJ hw
  obtain ⟨he,hf,_,_⟩ := cut_block_mass_identities A I J 2 u v w 5 hmass hrI hcJ hw
  have hIc : Iᶜ.card = 3 := by rw [Finset.card_compl, hI]; norm_num
  have hJc : Jᶜ.card = 3 := by rw [Finset.card_compl, hJ]; norm_num
  have hrIc : (∑ i ∈ Iᶜ, rowSum A i) = 3+u := by
    have h := Finset.sum_add_sum_compl I (rowSum A)
    change _ = totalMass A at h
    rw [hmass,hrI] at h
    linarith
  have hcJc : (∑ j ∈ Jᶜ, colSum A j) = 3-v := by
    have h := Finset.sum_add_sum_compl J (colSum A)
    rw [← totalMass_eq_sum_colSum,hmass,hcJ] at h
    linarith
  have hRcomp : (∏ i ∈ Iᶜ, rowSum A i) ≤ (1+u/3)^3 := by
    have h := finite_subset_product_le_mean_pow (rowSum A) (rowSum_nonneg hA) Iᶜ (by omega)
    rw [hIc,hrIc] at h
    convert h using 1; first | rfl | ring
  have hCcomp : (∏ j ∈ Jᶜ, colSum A j) ≤ (1-v/3)^3 := by
    have h := finite_subset_product_le_mean_pow (colSum A) (colSum_nonneg hA) Jᶜ (by omega)
    rw [hJc,hcJc] at h
    convert h using 1; first | rfl | ring
  have hRI : (∏ i ∈ I, rowSum A i) ≤ (1-u/2)^2 := by
    have h := finite_subset_product_le_mean_pow (rowSum A) (rowSum_nonneg hA) I (by omega)
    rw [hI,hrI] at h
    convert h using 1; first | rfl | ring
  have hCJ : (∏ j ∈ J, colSum A j) ≤ (1+v/2)^2 := by
    have h := finite_subset_product_le_mean_pow (colSum A) (colSum_nonneg hA) J (by omega)
    rw [hJ,hcJ] at h
    convert h using 1; first | rfl | ring
  have hs : 0 < 1-v/3 := by linarith
  have ha : 0 < 1-u/2 := by linarith
  have hr : 0 < 1+u/3 := by linarith
  have hb : 0 < 1+v/2 := by linarith
  have hcJfloor (j) (hj : j ∈ J) : 1-v/3 ≤ colSum A j := by
    have h := horder.chosen_col_floor (by omega) j hj
    rw [hcJc,hJc] at h
    convert h using 1; first | rfl | ring
  have hrIcfloor (i) (hi : i ∈ Iᶜ) : 1-u/2 ≤ rowSum A i := by
    have h := horder.complementary_row_floor (by omega) i hi
    rw [hrI,hI] at h
    convert h using 1; first | rfl | ring
  have hsmallR := cut_row_product_lower_of_complement_upper A hA I J (79/100) ((1+u/3)^3)
    (by norm_num) (pow_pos hr 3) (fun i _ => hrL i) hRcomp (by rw [he]; linarith)
  have hsmallC := cut_col_product_lower_of_complement_upper A hA I J (1-v/3) ((1-v/3)^3)
    hs (pow_pos hs 3) hcJfloor hCcomp (by rw [hf]; linarith)
  have hlargeR := cut_row_product_lower_of_complement_upper A hA Iᶜ Jᶜ (1-u/2) ((1-u/2)^2)
    ha (pow_pos ha 2) hrIcfloor (by simpa only [compl_compl] using hRI)
    (by rw [compl_compl,hf]; linarith)
  have hlargeC := cut_col_product_lower_of_complement_upper A hA Iᶜ Jᶜ (79/100) ((1+v/2)^2)
    (by norm_num) (pow_pos hb 2) (fun j _ => hcL j) (by simpa only [compl_compl] using hCJ)
    (by rw [compl_compl,he]; linarith)
  rw [he] at hsmallR
  rw [hf] at hsmallC
  rw [compl_compl,hf] at hlargeR
  rw [compl_compl,he] at hlargeC
  have heqS : (1-((w+u+v)/2)/(1-v/3))/(1-v/3)^3 = fiveSmallColFactor u v w := by
    unfold fiveSmallColFactor
    generalize 1-v/3 = s at *
    field_simp [hs.ne']
  have heqA : (1-((w+u+v)/2)/(1-u/2))/(1-u/2)^2 = fiveLargeRowFactor u v w := by
    unfold fiveLargeRowFactor
    generalize 1-u/2 = a at *
    field_simp [ha.ne']
  rw [heqS] at hsmallC
  rw [heqA] at hlargeR
  exact ⟨hsmallR,hsmallC,hlargeR,hlargeC⟩

end DittertRybin
