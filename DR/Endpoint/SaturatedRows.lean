import DR.Endpoint.SaturatedScalarBounds
import DR.ElementarySymmetricBounds

/-! Reciprocal spread confines the actual positive mass-one row vector.
The interval variance bound sums the product of the two distances to the
interval endpoints; it is stronger than separate coordinate excursions. -/

namespace DittertRybin
open scoped BigOperators

theorem saturated_row_square_cap {m : ℕ} (hm : 0 < m) (r : Fin m → ℝ)
    (i : Fin m) :
    (r i)^2 ≤ 2*(1+(m : ℝ)^2*marginalVariance r)/(m : ℝ)^2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hi : (r i-1/(m : ℝ))^2 ≤ marginalVariance r :=
    Finset.single_le_sum (fun j _ => sq_nonneg (r j-1/(m : ℝ))) (Finset.mem_univ i)
  have haux (u c V : ℝ) (hh : (u-c)^2 ≤ V) : u^2 ≤ 2*V+2*c^2 := by
    nlinarith only [hh,sq_nonneg (u-2*c)]
  have h := haux (r i) (1/(m : ℝ)) (marginalVariance r) hi
  apply h.trans_eq
  field_simp
  ring

/-- Weighted averaging of all reciprocal pair bounds controls each reciprocal. -/
theorem saturated_reciprocal_interval {m : ℕ} (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∑ i, r i = 1) {L : ℝ}
    (hspread : ∀ i j, |1/r i-1/r j| < L) (i : Fin m) :
    (m : ℝ)-L < 1/r i ∧ 1/r i < (m : ℝ)+L := by
  have hid : (∑ j, r j*(1/r i-1/r j)) = 1/r i-(m : ℝ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      mul_one_div_cancel (hr _).ne', Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, hs, one_mul]
  have hsumL : (∑ j, r j*L) = L := by rw [← Finset.sum_mul, hs, one_mul]
  have hsumNeg : (∑ j, r j*(-L)) = -L := by rw [← Finset.sum_mul, hs, one_mul]
  have hh := Finset.sum_lt_sum
    (fun j (_ : j ∈ Finset.univ) => (mul_lt_mul_of_pos_left (abs_lt.mp (hspread i j)).2 (hr j)).le)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (abs_lt.mp (hspread i i)).2 (hr i)⟩
  have hl := Finset.sum_lt_sum
    (fun j (_ : j ∈ Finset.univ) => (mul_lt_mul_of_pos_left (abs_lt.mp (hspread i j)).1 (hr j)).le)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (abs_lt.mp (hspread i i)).1 (hr i)⟩
  rw [hid, hsumL] at hh
  rw [hid, hsumNeg] at hl
  constructor <;> linarith

theorem saturated_row_interval {m : ℕ} (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∑ i, r i = 1) {L : ℝ}
    (hM : L < (m : ℝ)) (_hL : 0 ≤ L)
    (hspread : ∀ i j, |1/r i-1/r j| < L) (i : Fin m) :
    1/((m : ℝ)+L) < r i ∧ r i < 1/((m : ℝ)-L) := by
  have h := saturated_reciprocal_interval r hr hs hspread i
  have hp : 0 < (m : ℝ)+L := by linarith
  have hm : 0 < (m : ℝ)-L := by linarith
  constructor
  · apply (div_lt_iff₀ hp).mpr
    have hh := (div_lt_iff₀ (hr i)).mp h.2
    nlinarith only [hh]
  · apply (lt_div_iff₀ hm).mpr
    have hh := (lt_div_iff₀ (hr i)).mp h.1
    nlinarith only [hh]

theorem saturated_interval_variance_bound {m : ℕ} (hm : 0 < m)
    (r : Fin m → ℝ) (hs : ∑ i, r i = 1) {L : ℝ}
    (hL : 0 ≤ L) (hM : L < (m : ℝ))
    (hinterval : ∀ i, 1/((m : ℝ)+L) < r i ∧ r i < 1/((m : ℝ)-L)) :
    marginalVariance r < L^2/((m : ℝ)*((m : ℝ)^2-L^2)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (m : ℝ)+L ≠ 0 := ne_of_gt (by linarith)
  have hn : (m : ℝ)-L ≠ 0 := ne_of_gt (by linarith)
  have hden : (m : ℝ)^2-L^2 ≠ 0 := ne_of_gt (by nlinarith)
  have hsum : 0 < ∑ i, (r i-1/((m : ℝ)+L))*(1/((m : ℝ)-L)-r i) :=
    Finset.sum_pos (fun i _ => mul_pos (sub_pos.mpr (hinterval i).1)
      (sub_pos.mpr (hinterval i).2)) ⟨⟨0,hm⟩,Finset.mem_univ _⟩
  have hterm (i : Fin m) : (r i-1/((m : ℝ)+L))*(1/((m : ℝ)-L)-r i) =
      (1/((m : ℝ)-L)+1/((m : ℝ)+L))*r i-(r i)^2-
        1/((m : ℝ)+L)* (1/((m : ℝ)-L)) := by ring
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hid : 1/((m : ℝ)-L)+1/((m : ℝ)+L)-
      (m : ℝ)*(1/((m : ℝ)+L)*(1/((m : ℝ)-L)))-1/(m : ℝ) =
      L^2/((m : ℝ)*((m : ℝ)^2-L^2)) := by
    field_simp
    ring
  rw [marginalVariance_eq_sum_sq hm hs, ← hid]
  linarith

/-- Reciprocal stationarity and the exact variance certificate imply the
strict scalar condition for the original complementary-product kernel. -/
theorem saturated_rows_psd_criterion {m : ℕ} (hm : 96 ≤ m)
    (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (hs : ∑ i, r i = 1)
    {a gamma : ℝ} (ha : a < 1/1000)
    (hgamma : gamma ≤ a/((m : ℝ)*((m : ℝ)-1)))
    (hspread : ∀ i j, |1/r i-1/r j| < (1184/121 : ℝ)) :
    ((m : ℝ)-1)*((∑ i, (r i)^2)+gamma) < 1 := by
  have hm0 : 0 < m := by omega
  have hmR : (96 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR0 : (0 : ℝ) < m := by linarith
  have hm1 : 0 < (m : ℝ)-1 := by linarith
  have hML : (1184/121 : ℝ) < m := by linarith
  have hd : 0 < (m : ℝ)^2-(1184/121 : ℝ)^2 := by nlinarith
  have hV := saturated_interval_variance_bound hm0 r hs (by norm_num : (0 : ℝ)≤1184/121)
    hML (saturated_row_interval r hr hs hML (by norm_num) hspread)
  have hgap := saturated_variance_scalar_gap hmR ha
  have hratio : (1184/121 : ℝ)^2/((m : ℝ)^2-(1184/121 : ℝ)^2) <
      (1-a)/((m : ℝ)-1) := (div_lt_div_iff₀ hd hm1).mpr hgap
  have hscaled := div_lt_div_of_pos_right hratio hmR0
  have heq : (1184/121 : ℝ)^2/((m : ℝ)^2-(1184/121 : ℝ)^2)/(m : ℝ) =
      (1184/121 : ℝ)^2/((m : ℝ)*((m : ℝ)^2-(1184/121 : ℝ)^2)) := by
    field_simp
  rw [heq] at hscaled
  have hv := hV.trans hscaled
  rw [marginalVariance_eq_sum_sq hm0 hs] at hv
  have hcombined : (∑ i, (r i)^2)+gamma < 1/(m : ℝ)+
      (1-a)/((m : ℝ)-1)/(m : ℝ)+a/((m : ℝ)*((m : ℝ)-1)) := by linarith
  have hend : 1/(m : ℝ)+(1-a)/((m : ℝ)-1)/(m : ℝ)+
      a/((m : ℝ)*((m : ℝ)-1)) = 1/((m : ℝ)-1) := by
    field_simp
    ring
  rw [hend] at hcombined
  have hprod := (lt_div_iff₀ hm1).mp hcombined
  nlinarith only [hprod]

end DittertRybin
