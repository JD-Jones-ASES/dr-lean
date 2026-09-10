import DR.Endpoint.TwoZeroPermanent

namespace DittertRybin

/-- Every extra zero is allowed: an identity matrix lies in the domain. -/
example : boundaryPermanentFloor 27*(1+1/(4*(25 : ℝ)^2)) <
    (1 : Matrix (Fin 27) (Fin 27) ℝ).permanent := by
  apply permanent_two_zero_tail_gap (n := 25) (by decide)
    (by simp)
    (0 : Fin 27) 1 1 0 (by decide) (by decide)
  · simp
  · simp

example {N : ℕ} (hN : 27 ≤ N) (D : Board N N)
    (hD : D ∈ doublyStochastic ℝ (Fin N))
    (hz : ∃ i₁ i₂ j₁ j₂, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧ D i₁ j₁=0 ∧ D i₂ j₂=0) :
    boundaryPermanentFloor N*(1+1/(4*((N : ℝ)-2)^2)) < D.permanent :=
  permanent_two_independent_zero_gap hN hD hz

/-- The scalar representative is obtained from a matrix, not supplied as a premise. -/
example {n : ℕ} (hn : 2 ≤ n) (D : Board (n+2) (n+2))
    (hD : D ∈ doublyStochastic ℝ (Fin (n+2)))
    (i₁ i₂ j₁ j₂ : Fin (n+2)) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hz₁ : D i₁ j₁=0) (hz₂ : D i₂ j₂=0) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1/(n : ℝ) ∧ 0 ≤ b ∧ b ≤ 1/(n : ℝ) ∧
      twoZeroReducedPermanent n a b ≤ D.permanent :=
  twoZeroReducedPermanent_representative hn hD i₁ i₂ j₁ j₂ hi hj hz₁ hz₂

example {D : Board 22 22} (hD : D ∈ doublyStochastic ℝ (Fin 22))
    (i₁ i₂ j₁ j₂ : Fin 22) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hz₁ : D i₁ j₁=0) (hz₂ : D i₂ j₂=0) :
    (Certificates.nearEndpointPermanentFloorRat 21 : ℝ) < D.permanent :=
  permanent_two_zero_finite_gap (n := 21) (by decide) (by decide) hD
    i₁ i₂ j₁ j₂ hi hj hz₁ hz₂

example {D : Board 26 26} (hD : D ∈ doublyStochastic ℝ (Fin 26))
    (i₁ i₂ j₁ j₂ : Fin 26) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hz₁ : D i₁ j₁=0) (hz₂ : D i₂ j₂=0) :
    (Certificates.nearEndpointPermanentFloorRat 25 : ℝ) < D.permanent :=
  permanent_two_zero_finite_gap (n := 25) (by decide) (by decide) hD
    i₁ i₂ j₁ j₂ hi hj hz₁ hz₂

/-- A shared row is not a pair of independent prescribed zeros. -/
example : ¬((0 : Fin 27) ≠ 0 ∧ (1 : Fin 27) ≠ 2) := by simp

#print axioms twoZeroReducedPermanent_representative
#print axioms permanent_two_zero_tail_gap
#print axioms permanent_two_independent_zero_gap
#print axioms permanent_two_zero_finite_gap

end DittertRybin
