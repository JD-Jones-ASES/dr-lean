import DR.Endpoint.TwoZeroPolynomialBracket

namespace DittertRybin.Tests

-- One exceptional diagonal vanishes; unequal parameters strictly improve.
example : twoZeroReducedPermanent 4 (1/4) 0 = 81/2048 ∧
    twoZeroReducedPermanent 4 (1/8) (1/8) = 81/4096 := by
  norm_num [twoZeroReducedPermanent,Nat.factorial]

example : ¬twoZeroReducedPermanent 4 (1/4) 0 ≤
    twoZeroReducedPermanent 4 (1/8) (1/8) := by
  norm_num [twoZeroReducedPermanent,Nat.factorial]

-- Both exceptional diagonals vanish, and the border-zero corner is retained.
example : twoZeroReducedPermanent 4 (1/4) (1/4) = 9/512 ∧
    twoZeroReducedPermanent 4 0 0 = 3/32 := by
  norm_num [twoZeroReducedPermanent,Nat.factorial]

example : twoZeroReducedPermanent 4 (1/8) (1/8) < twoZeroReducedPermanent 4 (1/4) 0 := by
  have h := twoZeroReducedPermanent_equalize_lt (m := 4) (a := 1/4) (b := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

-- Polynomial identities themselves retain signed, infeasible parameters.
example : twoZeroReducedPermanent 4 (1/2) (-1/4) = 1539/4096 := by
  norm_num [twoZeroReducedPermanent,Nat.factorial]

example (u : ℝ) : twoZeroReducedPermanent 4 ((1-u)/4) ((1-u)/4) =
    twoZeroUnivariate 4 u := twoZeroReducedPermanent_diagonal (by norm_num) u

-- The m^4 numerator normalization cannot be omitted.
example : twoZeroH 4 0 = 3/64 ∧ twoZeroG 4 0 = 12 ∧ ¬twoZeroH 4 0 = twoZeroG 4 0 := by
  norm_num [twoZeroH,twoZeroX,twoZeroG]

-- Convexity and cubic strict monotonicity are global in the real score.
example : 0 < twoZeroCubicDeriv 4 (-7) ∧ 0 < twoZeroGSecond 4 37 :=
  ⟨twoZeroCubicDeriv_pos (by norm_num) _,twoZeroGSecond_pos (by norm_num) _⟩

example : twoZeroCubic 4 (7/32) = -141/1024 ∧ twoZeroCubic 4 (1/4) = 1/4 := by
  norm_num [twoZeroCubic]

-- The upper endpoint cannot be used as a lower sign-certified endpoint.
example : ¬twoZeroCubic 4 (1/4) ≤ 0 := by norm_num [twoZeroCubic]

example : twoZeroUnivariate 4 0 = 9/512 ∧ twoZeroUnivariate 4 1 = 3/32 := by
  norm_num [twoZeroUnivariate,twoZeroX,twoZeroH,Nat.factorial]

-- A fully evaluated rational floor applies to all parameters, including edges.
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ 1/4) (hb' : b ≤ 1/4) :
    (31941/2097152 : ℝ) ≤ twoZeroReducedPermanent 4 a b := by
  have h := twoZeroReducedPermanent_coarse_lower (by norm_num : 4 ≤ 4) ha hb ha' hb'
  norm_num [twoZeroX,twoZeroH,Nat.factorial] at h
  exact h

example {m : ℕ} (hm : 4 ≤ m) {a b ell r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/(m : ℝ)) (hbM : b ≤ 1/(m : ℝ))
    (hl : 0 ≤ ell) (hlr : ell ≤ r) (hr : r ≤ 1/(m : ℝ))
    (hfl : twoZeroCubic m ell ≤ 0) (hfr : 0 ≤ twoZeroCubic m r) :
    (m.factorial : ℝ)*(twoZeroX m ell)^(m-2)*twoZeroH m r ≤
      twoZeroReducedPermanent m a b :=
  twoZeroReducedPermanent_lower_of_bracket hm ha hb haM hbM hl hlr hr hfl hfr

#print axioms twoZeroReducedPermanent_equalization_identity
#print axioms twoZeroReducedPermanent_equalize
#print axioms twoZeroReducedPermanent_equalize_lt
#print axioms hasDerivAt_twoZeroUnivariate
#print axioms twoZeroCubic_strictMono
#print axioms twoZeroH_antitoneOn
#print axioms twoZeroReducedPermanent_lower_of_bracket
#print axioms twoZeroCubic_uniform_bracket
#print axioms twoZeroReducedPermanent_coarse_lower
end DittertRybin.Tests
