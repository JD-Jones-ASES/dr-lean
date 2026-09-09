import DR.Rectangular.FourRowMinorantEqualRows

/-! The homogeneous boundary inputs for the fixed-moment three-face reduction. -/

namespace DittertRybin
open scoped BigOperators

/-- Positive arbitrary row mass is normalized explicitly; no unit-mass factor is omitted. -/
theorem fourRowMinorantHomogeneous_pair_nonneg_of_pos_mass (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hm : 0 < ∑ i, r i)
    (hv : ∀ i, 0 ≤ v i) (hsv : ∑ i, v i = 1)
    (i j : Fin 4) (hij : i ≠ j) (hsupp : ∀ k, k ≠ i → k ≠ j → v k = 0) :
    0 ≤ fourRowMinorantHomogeneous r v := by
  let S := ∑ i, r i
  let p := fun i => r i/S
  have hp : ∀ i, 0 ≤ p i := fun i => div_nonneg (hr i) hm.le
  have hps : ∑ i, p i = 1 := by
    dsimp [p]
    rw [←Finset.sum_div]
    exact div_self hm.ne'
  have heq : r = fun i => S*p i := by
    funext i
    dsimp [p]
    field_simp [show S ≠ 0 from hm.ne']
  have h := fourRowMinorantHomogeneous_pair_nonneg p v hp hps hv hsv i j hij hsupp
  rw [heq,fourRowMinorantHomogeneous_smul]
  exact mul_nonneg (pow_nonneg hm.le 3) h

private theorem repeated_active_12 (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i, v i = 1)
    (h3 : v 3 = 0) (h12 : r 1 = r 2) : 0 ≤ fourRowMinorantHomogeneous r v := by
  have heqr : r = ![r 0,r 1,r 1,r 3] := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_two,Matrix.cons_val_three,h12]
  have heqv : v = ![v 0,v 1,v 2,0] := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_two,Matrix.cons_val_three,h3]
  have hs : v 0+v 1+v 2=1 := by
    simp [Fin.sum_univ_succ,h3] at hvs
    linarith
  have h := fourRowMinorantHomogeneous_equal_rows_nonneg (hr 0).le (hr 1) (hr 3).le
    (hv 0) (hv 1) (hv 2) hs
  rwa [←heqr,←heqv] at h

/-- Any repeated active row pair on the proper face is covered by the actual
certificate, with arbitrary positive row masses and arbitrary column probabilities. -/
theorem fourRowMinorantHomogeneous_repeated_active_nonneg (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i, v i = 1)
    (h3 : v 3 = 0) (hrep : r 0=r 1 ∨ r 0=r 2 ∨ r 1=r 2) :
    0 ≤ fourRowMinorantHomogeneous r v := by
  classical
  rcases hrep with h01 | h02 | h12
  · let e := Equiv.swap (0 : Fin 4) 2
    have h := repeated_active_12 (r ∘ e) (v ∘ e)
      (fun i => hr (e i)) (fun i => hv (e i)) ((Equiv.sum_comp e v).trans hvs)
      (by simpa [e,Function.comp_apply,Equiv.swap_apply_def] using h3)
      (by simpa [e,Function.comp_apply,Equiv.swap_apply_def] using h01.symm)
    rwa [fourRowMinorantHomogeneous_permute] at h
  · let e := Equiv.swap (0 : Fin 4) 1
    have h := repeated_active_12 (r ∘ e) (v ∘ e)
      (fun i => hr (e i)) (fun i => hv (e i)) ((Equiv.sum_comp e v).trans hvs)
      (by simpa [e,Function.comp_apply,Equiv.swap_apply_def] using h3)
      (by simpa [e,Function.comp_apply,Equiv.swap_apply_def] using h02)
    rwa [fourRowMinorantHomogeneous_permute] at h
  · exact repeated_active_12 r v hr hv hvs h3 h12

end DittertRybin
