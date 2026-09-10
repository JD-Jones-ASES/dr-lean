import DR.Endpoint.TransitionBootstrap
import DR.Endpoint.TransitionDeletionBalance
import DR.Endpoint.LLLStripDeletion

/-! Actual retained-board estimates throughout the accepted transition
interval. The original-row LLL comparison is used only to obtain the row
budget; the retained board is then independently normalized. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_transition_lower_square {m n : ℕ} (hm : 10^18≤m)
    (hlower : m*(m-1)≤20*n) : 4096*m^3≤n^2 := by
  have hm2 : 2≤m := by omega
  have hsq : m^2≤40*n := by
    have h := Nat.mul_le_mul_left m (by omega : m≤2*(m-1))
    nlinarith
  have hsq2 := Nat.mul_self_le_mul_self hsq
  have hpow := Nat.mul_le_mul_left (m^3) (by omega : 6553600≤m)
  nlinarith

theorem endpoint_transition_contender_column_cap {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hupper : n≤10000*m^2) {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) (j : Fin n) :
    colSum P j<2/(n:ℝ) := by
  have hmR : (10^18:ℝ)≤m := by exact_mod_cast hm
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hnR : (n:ℝ)≤10000*(m:ℝ)^2 := by exact_mod_cast hupper
  have hm2 : (10000:ℝ)≤(m:ℝ)^2 := by nlinarith
  have hn4 : (n:ℝ)≤(m:ℝ)^4 := by
    nlinarith [mul_nonneg (sq_nonneg (m:ℝ)) (sub_nonneg.mpr hm2)]
  have hinv : 1/(m:ℝ)^4≤1/(n:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hn0 hn4
  have h := endpoint_contender_column_cap_large (by omega) hmn hP hcont j
  calc
    colSum P j<1/(n:ℝ)+1/(m:ℝ)^4 := h
    _≤1/(n:ℝ)+1/(n:ℝ) := add_le_add le_rfl hinv
    _=2/(n:ℝ) := by ring

theorem endpoint_transition_deleted_bounds {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (a b : Fin n) (hab : a≠b) :
    let T := keepColumns P ({a,b}ᶜ)
    let h := totalMass T
    (15/16:ℝ)<h ∧ (∀ i,0<rowSum T i) ∧
    (∑ i,(1-(m:ℝ)*(rowSum T i/h))^2)<1/9 ∧
    (∀ j,colSum (normalizeRows T) j≤4*(m:ℝ)/(n:ℝ)) ∧
    ((m-2:ℕ):ℝ)*(2/(n:ℝ))≤h/2 := by
  let T := keepColumns P ({a,b}ᶜ)
  let h := totalMass T
  have hm1 : 1≤m := by omega
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm1
  have hm0 : (0:ℝ)<m := by linarith
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlow := endpoint_transition_lower_square hm hlower
  have hc := endpoint_transition_contender_column_cap hm hmn hupper hP hcont
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
    (mul_lt_mul_of_pos_left hw hm0).trans_le (endpoint_strip_deletion_scale hm1 hlow)
  have hh : (15/16:ℝ)<h := by nlinarith
  have hh0 : 0<h := by linarith
  have hr := endpoint_transition_scaled_row_sq_lt hm hmn hlower hupper hP hcont
  have hsq := transition_kept_row_sq_lt hm1 hP ({a,b}ᶜ) hmw.le hr
  change (∑ i,(1-(m:ℝ)*(rowSum T i/h))^2)<1/9 at hsq
  have hrs (i : Fin m) : (2/3:ℝ)/(m:ℝ)<rowSum T i/h :=
    endpoint_row_lower_of_sq (by omega) _ hsq i
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
  have hfactor := endpoint_strip_deletion_scale hm1 hlow
  have hseq : ((m-2:ℕ):ℝ)*(2/(n:ℝ))≤h/2 := by
    have hmul := mul_le_mul_of_nonneg_right hk (by positivity : 0≤2/(n:ℝ))
    have heq : (m:ℝ)*(4/(n:ℝ))=2*((m:ℝ)*(2/(n:ℝ))) := by ring
    nlinarith
  exact ⟨hh,fun i => hR.trans (hrR i),hsq,hnorm,hseq⟩

end DittertRybin
