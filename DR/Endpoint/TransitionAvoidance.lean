import DR.Endpoint.TransitionCollisionBounds

/-! The refined local lemma compares the actual original-row avoidance
probability with uniform avoidance throughout the accepted transition
range. Deleted-row avoidance is not substituted anywhere in this chain. -/
namespace DittertRybin

theorem endpoint_transition_original_log_bound {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    0<originalRowAvoidance P ∧
    -Real.log (originalRowAvoidance P)≤(m:ℝ)^2/(2*(n:ℝ))+6000000000/(m:ℝ) := by
  have hmR : (10^18:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlow : (m:ℝ)*((m:ℝ)-1)≤20*(n:ℝ) := by
    have hc : ((m*(m-1):ℕ):ℝ)≤((20*n:ℕ):ℝ) := by exact_mod_cast hlower
    simpa only [Nat.cast_mul,Nat.cast_sub (by omega : 1≤m),Nat.cast_one,Nat.cast_ofNat] using hc
  have hs20 : (m:ℝ)^2/(2*(n:ℝ))≤20 := by
    apply (div_le_iff₀ (by positivity : 0<2*(n:ℝ))).mpr
    nlinarith
  have hd0 : (0:ℝ)≤6200000/(m:ℝ) := by positivity
  have hd : (6200000:ℝ)/(m:ℝ)≤1/8 := by
    apply (div_le_iff₀ hm0).mpr
    linarith
  obtain ⟨hload,hD⟩ := endpoint_transition_collision_bounds hm hmn hlower hupper hP hcont
  have hr := endpoint_contender_rows_pos (by omega) hmn hP hcont
  have hX := normalizeRows_nonneg P hP.1
  have hsX := normalizeRows_rowSum P (fun i => (hr i).ne')
  have hp := rowAvoidance_pos_of_collisionLoad (normalizeRows P) hX hsX
    (fun i => (hload i).trans hd)
  have hlog := neg_log_rowAvoidance_le (normalizeRows P) hX hsX (6200000/(m:ℝ)) hd0 hd hload
  refine ⟨hp,?_⟩
  exact hlog.trans (transition_log_denominator_bound (m:ℝ) ((m:ℝ)^2/(2*(n:ℝ)))
    (rowCollisionIntensity (normalizeRows P)) hmR hs20 hD)

/-- This is the comparison of original row avoidance, not the avoidance
of any column-deleted board used later in the curvature argument. -/
theorem endpoint_transition_original_avoidance_relative {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    distinctUniformProbability n m*Real.exp (-7000000000/(m:ℝ))≤originalRowAvoidance P := by
  have hmR : (10^18:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlow : (m:ℝ)*((m:ℝ)-1)≤20*(n:ℝ) := by
    have hc : ((m*(m-1):ℕ):ℝ)≤((20*n:ℕ):ℝ) := by exact_mod_cast hlower
    simpa only [Nat.cast_mul,Nat.cast_sub (by omega : 1≤m),Nat.cast_one,Nat.cast_ofNat] using hc
  have hsqn : (m:ℝ)^2≤40*(n:ℝ) := by nlinarith
  obtain ⟨hp,hlog⟩ := endpoint_transition_original_log_bound hm hmn hlower hupper hP hcont
  have hexp : Real.exp (-((m:ℝ)^2/(2*(n:ℝ))+6000000000/(m:ℝ)))≤originalRowAvoidance P := by
    rw [← Real.exp_log hp]
    apply Real.exp_le_exp.mpr
    linarith
  have hb := distinctUniformProbability_le_exp (by omega) hmn
  calc
    _≤Real.exp (-((m:ℝ)*((m:ℝ)-1)/(2*(n:ℝ))))*
        Real.exp (-7000000000/(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _=Real.exp (-((m:ℝ)*((m:ℝ)-1)/(2*(n:ℝ)))-7000000000/(m:ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _≤Real.exp (-((m:ℝ)^2/(2*(n:ℝ))+6000000000/(m:ℝ))) := by
      apply Real.exp_le_exp.mpr
      field_simp
      nlinarith
    _≤originalRowAvoidance P := hexp

end DittertRybin
