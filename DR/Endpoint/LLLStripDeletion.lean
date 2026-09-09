import DR.Endpoint.LLLStripParameters
import DR.Endpoint.DeletedRowBalance

/-! Actual contender and retained-board estimates for the accepted LLL
strip. Row normalization always applies to the supplied retained board,
not to the original contender's row law. -/
namespace DittertRybin
open scoped BigOperators

theorem normalizeRows_column_cap_of_row_lower {m n : ℕ} (P : Board m n)
    (hP : ∀ i j,0≤P i j) (R c : ℝ) (hR : 0<R)
    (hr : ∀ i,R≤rowSum P i) (hc : ∀ j,colSum P j≤c) (j : Fin n) :
    colSum (normalizeRows P) j≤c/R := by
  calc
    _≤∑ i,P i j/R := by
      apply Finset.sum_le_sum
      intro i _
      exact div_le_div_of_nonneg_left (hP i j) hR (hr i)
    _=colSum P j/R := by simp only [colSum,Finset.sum_div]
    _≤c/R := div_le_div_of_nonneg_right (hc j) hR.le

theorem endpoint_strip_deleted_bounds {m n : ℕ} (hm : 128≤m)
    (hlower : 4096*m^3≤n^2) (hupper : 20*n≤m*(m-1))
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (a b : Fin n) (hab : a≠b) :
    let T := keepColumns P ({a,b}ᶜ)
    let h := totalMass T
    (15/16:ℝ)<h ∧
    (∀ i,0<rowSum T i) ∧
    (∑ i,(1-(m:ℝ)*(rowSum T i/h))^2)<1/81 ∧
    (∀ j,colSum (normalizeRows T) j≤4*(m:ℝ)/(n:ℝ)) ∧
    ((m-2:ℕ):ℝ)*(2/(n:ℝ))≤h/2 := by
  let T := keepColumns P ({a,b}ᶜ)
  let h := totalMass T
  have hm1 : 1≤m := by omega
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm1
  have hm0 : (0:ℝ)<m := by linarith
  have hmn : m≤n := by have := endpoint_strip_n_ge hm1 hlower; omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hc := endpoint_strip_contender_column_cap hm hmn hupper hP hcont
  have hmass : h=1-colSum P a-colSum P b := by
    dsimp only [h,T]
    rw [totalMass_delete_two P a b hab,hP.2]
  have hw0 : 0≤1-h := by
    rw [hmass]
    linarith [colSum_nonneg hP.1 a,colSum_nonneg hP.1 b]
  have hw : 1-h<4/(n:ℝ) := by
    rw [hmass]
    have ha := hc a
    have hb := hc b
    have hid : 2/(n:ℝ)+2/(n:ℝ)=4/(n:ℝ) := by ring
    linarith
  have hmw : (m:ℝ)*(1-h)<1/16 :=
    (mul_lt_mul_of_pos_left hw hm0).trans_le (endpoint_strip_deletion_scale hm1 hlower)
  have hh : (15/16:ℝ)<h := by nlinarith
  have hh0 : 0<h := by linarith
  have hb := distinctUniformProbability_small_of_twenty_mul_le (by omega) hmn hupper
  have hr := endpoint_contender_scaled_row_sq_small (by omega) hmn hP hcont hb.le
  have hsq := endpoint_kept_row_sq_lt hm1 hP ({a,b}ᶜ) hmw.le hr
  change (∑ i,(1-(m:ℝ)*(rowSum T i/h))^2)<1/81 at hsq
  have hrs (i : Fin m) : (2/3:ℝ)/(m:ℝ)<rowSum T i/h :=
    endpoint_row_lower_of_sq (by omega) _ (hsq.trans (by norm_num)) i
  let R := ((2/3:ℝ)/(m:ℝ))*h
  have hR : 0<R := by dsimp only [R]; positivity
  have hrR (i : Fin m) : R<rowSum T i := (lt_div_iff₀ hh0).mp (hrs i)
  have hT := keepColumns_nonneg hP.1 ({a,b}ᶜ)
  have hcT (j : Fin n) : colSum T j≤2/(n:ℝ) :=
    (colSum_keepColumns_le hP.1 ({a,b}ᶜ) j).trans (hc j).le
  have hratio : (2/(n:ℝ))/R≤4*(m:ℝ)/(n:ℝ) := by
    apply (div_le_iff₀ hR).mpr
    dsimp only [R]
    field_simp
    nlinarith
  have hnorm (j : Fin n) : colSum (normalizeRows T) j≤4*(m:ℝ)/(n:ℝ) :=
    (normalizeRows_column_cap_of_row_lower T hT R (2/(n:ℝ)) hR
      (fun i => (hrR i).le) hcT j).trans hratio
  have hk : ((m-2:ℕ):ℝ)≤m := by exact_mod_cast Nat.sub_le m 2
  have hfactor := endpoint_strip_deletion_scale hm1 hlower
  have hseq : ((m-2:ℕ):ℝ)*(2/(n:ℝ))≤h/2 := by
    have hmul := mul_le_mul_of_nonneg_right hk (by positivity : 0≤2/(n:ℝ))
    have heq : (m:ℝ)*(4/(n:ℝ))=2*((m:ℝ)*(2/(n:ℝ))) := by ring
    nlinarith
  exact ⟨hh,fun i => hR.trans (hrR i),hsq,hnorm,hseq⟩

end DittertRybin
