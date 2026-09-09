import DR.Certificates.FourRowScalarGaugeData

/-! The quantitative scalar gauge inequality on the whole closed four-row simplex. -/

namespace DittertRybin
open scoped BigOperators

/-- The polynomial certificate applies to every nonnegative row vector, after sorting. -/
theorem fourRowGaugeHomogeneous_variance_lower (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (61/256)*fourRowGaugeHomogeneousVariance r*(∑ i, r i)^5 ≤ fourRowGaugeHomogeneous r := by
  let e := Tuple.sort r
  let u := r ∘ e
  have hm : Monotone u := Tuple.monotone_sort r
  let a := u 3-u 2
  let b := u 2-u 1
  let c := u 1-u 0
  let d := u 0
  have ha : 0 ≤ a := sub_nonneg.mpr (hm (by decide : (2:Fin 4) ≤ 3))
  have hb : 0 ≤ b := sub_nonneg.mpr (hm (by decide : (1:Fin 4) ≤ 2))
  have hc : 0 ≤ c := sub_nonneg.mpr (hm (by decide : (0:Fin 4) ≤ 1))
  have hd : 0 ≤ d := hr (e 0)
  have hshape : u = ![d,c+d,b+c+d,a+b+c+d] := by
    funext i
    fin_cases i <;> simp [a,b,c,d]
  have hmass : ∑ i, u i = a+2*b+3*c+4*d := by
    simp [Fin.sum_univ_four,a,b,c,d]
    ring
  have hid := fourRowScalarGaugeResidual_identity a b c d
  rw [← hshape,← hmass] at hid
  have hp := fourRowScalarGaugeResidual_nonneg ha hb hc hd
  have hbnd : (61/256)*fourRowGaugeHomogeneousVariance u*(∑ i, u i)^5 ≤
      fourRowGaugeHomogeneous u := by linarith only [hid,hp]
  dsimp only [u] at hbnd
  rw [fourRowGaugeHomogeneous_permute,fourRowGaugeHomogeneousVariance_permute] at hbnd
  simpa only [Function.comp_apply,Equiv.sum_comp e] using hbnd

/-- The elementary square-root minorant, including both endpoints of its domain. -/
theorem fourRowGauge_sqrt_minorant {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1/3) :
    2*(3/32)-2*x-(x-3/32)^2 ≤
      4*Real.sqrt (29/32)*(Real.sqrt (1-x)-Real.sqrt (29/32)) := by
  let y := Real.sqrt (1-x)
  let s := Real.sqrt (29/32)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hy2 : y^2 = 1-x := Real.sq_sqrt (by linarith)
  have hs2 : s^2 = 29/32 := Real.sq_sqrt (by norm_num)
  have hy : 1/2 ≤ y := by nlinarith
  have hs : 1/2 ≤ s := by nlinarith
  have hmul : (1/2:ℝ)*(1/2) ≤ y*s := mul_le_mul hy hs (by norm_num) hy0
  have hsum : 0 ≤ (y+s)^2-2 := by nlinarith
  have hp := mul_nonneg (sq_nonneg (y-s)) hsum
  have hu : x-3/32 = s^2-y^2 := by linarith
  have hid : 4*s*(y-s)+2*(x-3/32)+(x-3/32)^2 =
      (y-s)^2*((y+s)^2-2) := by rw [hu]; ring
  change _ ≤ 4*s*(y-s)
  nlinarith only [hp,hid]

/-- Quantitative scalar gauge bound for arbitrary nonnegative probability rows.
It assumes no matrix maximum, per-column minorant, or collision remainder. -/
theorem fourRowScalarGauge_gap (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) :
    29/32+(61/512)*fourRowMarginalVariance r ≤
      (∑ i, r i*fourRowGaugeWeight r i)^2 := by
  let s := Real.sqrt (29/32)
  let H := ∑ i, r i*fourRowGaugeWeight r i
  have hs2 : s^2 = 29/32 := Real.sq_sqrt (by norm_num)
  have hpoly := fourRowGaugeHomogeneous_variance_lower r hr
  rw [fourRowGaugeHomogeneousVariance_probability r hsum,hsum,one_pow,mul_one] at hpoly
  have hminor : fourRowGaugeHomogeneous r ≤ 4*s*(H-s) := by
    have hi (i : Fin 4) := fourRowGauge_sqrt_minorant
      (fourRowGaugeCollision_bounds r hr hsum i).1
      (show fourRowGaugeCollision r i ≤ 1/3 by linarith [(fourRowGaugeCollision_bounds r hr hsum i).2])
    have hweighted := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hr i))
    have hleft : fourRowGaugeHomogeneous r =
        ∑ i, r i*(2*(3/32)-2*fourRowGaugeCollision r i-(fourRowGaugeCollision r i-3/32)^2) := by
      simp only [fourRowGaugeHomogeneous,hsum,one_pow,mul_one]
      have hs : r 0+r 1+r 2+r 3 = 1 := by simpa [Fin.sum_univ_four,add_assoc] using hsum
      simp only [Fin.sum_univ_four]
      nlinarith only [hs]
    have hright : (∑ i, r i*(4*Real.sqrt (29/32)*(Real.sqrt (1-fourRowGaugeCollision r i)-Real.sqrt (29/32)))) =
        4*s*(H-s) := by
      change (∑ i, r i*(4*s*(fourRowGaugeWeight r i-s))) = _
      have he (i : Fin 4) : r i*(4*s*(fourRowGaugeWeight r i-s)) =
          4*s*(r i*fourRowGaugeWeight r i-r i*s) := by ring
      simp_rw [he]
      rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.sum_mul,hsum,one_mul]
    rw [← hleft,hright] at hweighted
    exact hweighted
  change 29/32+(61/512)*fourRowMarginalVariance r ≤ H^2
  nlinarith only [hpoly,hminor,hs2,sq_nonneg (H-s)]

/-- The scalar gauge attains its uniform value only at uniform row masses. -/
theorem fourRowScalarGauge_eq_iff (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) :
    (∑ i, r i*fourRowGaugeWeight r i)^2 = 29/32 ↔ ∀ i, r i = 1/4 := by
  constructor
  · intro he i
    have hg := fourRowScalarGauge_gap r hr hsum
    have hv := fourRowMarginalVariance_nonneg r
    have hz : fourRowMarginalVariance r = 0 := by linarith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (r j-1/4))).mp hz
      i (Finset.mem_univ i)
    nlinarith
  · intro he
    have hg (i : Fin 4) : fourRowGaugeCollision r i = 3/32 := by
      rw [fourRowGaugeCollision_moments]
      norm_num [he]
    simp only [fourRowGaugeWeight,hg,← Finset.sum_mul,hsum,one_mul]
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1-3/32)]
    norm_num

end DittertRybin
