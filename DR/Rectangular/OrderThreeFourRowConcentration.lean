import DR.Rectangular.OrderThreeFourRowInitial

/-! A rational centered-cubic bootstrap on the entire four-row contender simplex. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def orderThreeFourRowColumnVariance {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ j,(a j-(∑ k,a k)/n)^2

theorem orderThreeFourRow_centered_cubic {n : ℕ} (hn : 0<n) (a : Fin n → ℝ) :
    (∑ j,(3*a j^2-11*a j^3)) =
      3*(∑ j,a j)^2/n-11*(∑ j,a j)^3/(n:ℝ)^2+
        ∑ j,(a j-(∑ k,a k)/n)^2*(3-11*(a j+2*(∑ k,a k)/n)) := by
  have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  let H := ∑ j,a j
  let h := H/n
  have hc : (∑ j,(a j-h))=0 := by
    simp [Finset.sum_sub_distrib,h,H]
    field_simp
    ring
  have ht (j : Fin n) : 3*a j^2-11*a j^3 =
      3*h^2-11*h^3+(6*h-33*h^2)*(a j-h)+(a j-h)^2*(3-11*(a j+2*h)) := by ring
  simp_rw [ht,Finset.sum_add_distrib,← Finset.mul_sum,hc]
  simp only [mul_zero,add_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp [h,H]
  congr 1
  · field_simp
  · congr 1
    funext j
    ring

theorem orderThreeFourRow_centered_cubic_lower {n : ℕ} (hn : 960≤n) (a : Fin n → ℝ)
    (ha : ∀ j,a j≤177/2000) (hH : (∑ j,a j)≤1) :
    3*(∑ j,a j)^2/n-11*(∑ j,a j)^3/(n:ℝ)^2+2*orderThreeFourRowColumnVariance a≤
      ∑ j,(3*a j^2-11*a j^3) := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hnreal : (960:ℝ)≤n := by exact_mod_cast hn
  have hmean : (∑ j,a j)/n≤1/960 := by
    apply (div_le_iff₀ hnpos).mpr
    linarith only [hH,hnreal]
  have hcoef (j : Fin n) : 2≤3-11*(a j+2*(∑ k,a k)/n) := by
    rw [mul_div_assoc]
    linarith [ha j]
  rw [orderThreeFourRow_centered_cubic (by omega)]
  gcongr
  unfold orderThreeFourRowColumnVariance
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hcoef j) (sq_nonneg (a j-(∑ k,a k)/n))

/-- The exact negative uniform correction gives V*n²<5 and row variance*n<14. -/
theorem orderThreeFourRow_contender_variances {n : ℕ} (hn : 960≤n) {P : Board 4 n}
    (hP : IsProbability P) (hcont : separationProbability (uniformBoard 4 n) 3≤separationProbability P 3) :
    orderThreeFourRowColumnVariance (orderThreeFourRowColumnGauge P)*(n:ℝ)^2<5 ∧
      orderThreeFourRowVariance (rowSum P)*n<14 := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  let a := orderThreeFourRowColumnGauge P
  let H := ∑ j,a j
  let V := orderThreeFourRowColumnVariance a
  let ρ := orderThreeFourRowVariance (rowSum P)
  have ha0 (j : Fin n) : 0≤a j := (orderThreeFourRowColumnGauge_bounds P hP j).1
  have hH0 : 0≤H := Finset.sum_nonneg fun j _ => ha0 j
  have hH1 : H≤1 := orderThreeFourRowColumnGauge_sum_le_one P hP
  have hH3 : H^3≤1 := by simpa using pow_le_pow_left₀ hH0 hH1 3
  have hV0 : 0≤V := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hρ0 : 0≤ρ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hgap : 5/8+ρ/4≤H^2 := by
    dsimp [H,a,ρ]
    rw [orderThreeFourRowColumnGauge_sum]
    exact orderThreeFourRowGauge_sum_sq_lower (rowSum P) (rowSum_nonneg hP.1) hP.2
  have hlo := (orderThreeFourRow_centered_cubic_lower hn a
    (fun j => (orderThreeFourRow_contender_initial_cap hn hP hcont j).2.le) hH1).trans
      (orderThreeFourRow_failure_ge_gauge_cubic P hP)
  have hup := sub_le_sub_left hcont 1
  rw [orderThreeFourRow_failure_uniform (by omega)] at hup
  have hscaled := mul_le_mul_of_nonneg_right (hlo.trans hup) (sq_nonneg (n:ℝ))
  have hscale : (3*H^2/n-11*H^3/(n:ℝ)^2+2*V)*(n:ℝ)^2 =
      3*H^2*n-11*H^3+2*V*(n:ℝ)^2 := by field_simp
  have hscaleU : (15/(8*(n:ℝ))-5/(4*(n:ℝ)^2))*(n:ℝ)^2 = 15*(n:ℝ)/8-5/4 := by field_simp
  change (3*H^2/n-11*H^3/(n:ℝ)^2+2*V)*(n:ℝ)^2≤_ at hscaled
  rw [hscale,hscaleU] at hscaled
  have hgscaled := mul_le_mul_of_nonneg_right hgap hnpos.le
  have hρn : 0≤ρ*n := mul_nonneg hρ0 hnpos.le
  have hVn : 0≤V*(n:ℝ)^2 := mul_nonneg hV0 (sq_nonneg _)
  constructor <;> nlinarith only [hscaled,hgscaled,hH3,hρn,hVn]

/-- Both concentration inputs for strict actual pair averaging follow from the contender premise. -/
theorem orderThreeFourRow_contender_concentration {n : ℕ} (hn : 960≤n) {P : Board 4 n}
    (hP : IsProbability P) (hcont : separationProbability (uniformBoard 4 n) 3≤separationProbability P 3) :
    (∀ j,colSum P j<7/(n:ℝ)) ∧ orderThreeFourRowVariance (rowSum P)<1/64 := by
  obtain ⟨hV,hρ⟩ := orderThreeFourRow_contender_variances hn hP hcont
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hnreal : (960:ℝ)≤n := by exact_mod_cast hn
  have hρ0 : 0≤orderThreeFourRowVariance (rowSum P) := Finset.sum_nonneg fun i _ => sq_nonneg _
  constructor
  · intro j
    let a := orderThreeFourRowColumnGauge P
    let H := ∑ k,a k
    have hH : H≤1 := orderThreeFourRowColumnGauge_sum_le_one P hP
    have ha0 (k : Fin n) : 0≤a k := (orderThreeFourRowColumnGauge_bounds P hP k).1
    have hpart : (a j-H/n)^2≤orderThreeFourRowColumnVariance a :=
      Finset.single_le_sum (fun k _ => sq_nonneg (a k-H/n)) (Finset.mem_univ j)
    have hscaled := mul_le_mul_of_nonneg_right hpart (sq_nonneg (n:ℝ))
    have hid : ((n:ℝ)*a j-H)^2=(a j-H/n)^2*(n:ℝ)^2 := by field_simp
    rw [← hid] at hscaled
    have han : (n:ℝ)*a j<7/2 := by nlinarith only [hscaled,hV,hH]
    have han0 : 0≤(n:ℝ)*a j := mul_nonneg hnpos.le (ha0 j)
    have hasq := pow_le_pow_left₀ han0 han.le 2
    have hcol := (orderThreeFourRowColumnGauge_bounds P hP j).2.2
    have hcscaled := mul_le_mul_of_nonneg_right hcol (sq_nonneg (n:ℝ))
    apply (lt_div_iff₀ hnpos).mpr
    nlinarith only [hcscaled,hasq]
  · nlinarith only [hρ,hρ0,hnreal]

end DittertRybin
