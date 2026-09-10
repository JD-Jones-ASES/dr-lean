import DR.Endpoint.TwoZeroReducedCounting
import DR.Endpoint.TwoZeroReduction
import DR.Endpoint.TwoZeroLogTail
import DR.Endpoint.NearEndpointTwoZeroPolynomial

/-! The actual two-independent-zero permanent floor. The compact face
reduction, exact matrix count, and scalar inequalities are all proved inputs. -/

namespace DittertRybin

/-- An actual scalar representative below every matrix on the closed two-zero
domain. No minimizer form or permanent floor is assumed. -/
theorem twoZeroReducedPermanent_representative {n : ℕ} (hn : 2 ≤ n)
    {D : Board (n+2) (n+2)} (hD : D ∈ doublyStochastic ℝ (Fin (n+2)))
    (i₁ i₂ j₁ j₂ : Fin (n+2)) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hz₁ : D i₁ j₁ = 0) (hz₂ : D i₂ j₂ = 0) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1/(n : ℝ) ∧ 0 ≤ b ∧ b ≤ 1/(n : ℝ) ∧
      twoZeroReducedPermanent n a b ≤ D.permanent := by
  obtain ⟨a,b,ha,haN,hb,hbN,hper⟩ := twoZeroReducedBoard_representative
    (by omega : 0 < n) hD i₁ i₂ j₁ j₂ hi hj hz₁ hz₂
  refine ⟨a,b,ha,haN,hb,hbN,?_⟩
  rwa [twoZeroReducedBoard_permanent hn] at hper

/-- The quantitative strict gap above the sharp one-zero floor, on arbitrary
doubly stochastic matrices with two independent zero entries. -/
theorem permanent_two_zero_tail_gap {n : ℕ} (hn : 25 ≤ n)
    {D : Board (n+2) (n+2)} (hD : D ∈ doublyStochastic ℝ (Fin (n+2)))
    (i₁ i₂ j₁ j₂ : Fin (n+2)) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hz₁ : D i₁ j₁ = 0) (hz₂ : D i₂ j₂ = 0) :
    boundaryPermanentFloor (n+2)*(1+1/(4*(n : ℝ)^2)) < D.permanent := by
  obtain ⟨a,b,ha,haN,hb,hbN,hper⟩ := twoZeroReducedPermanent_representative
    (by omega : 2 ≤ n) hD i₁ i₂ j₁ j₂ hi hj hz₁ hz₂
  exact (twoZeroReducedPermanent_tail_gap hn ha hb haN hbN).trans_le hper

/-- The same strict gap indexed by the actual matrix order. -/
theorem permanent_two_independent_zero_gap {N : ℕ} (hN : 27 ≤ N)
    {D : Board N N} (hD : D ∈ doublyStochastic ℝ (Fin N))
    (hz : ∃ i₁ i₂ j₁ j₂, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧ D i₁ j₁ = 0 ∧ D i₂ j₂ = 0) :
    boundaryPermanentFloor N*(1+1/(4*((N : ℝ)-2)^2)) < D.permanent := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le (show 2 ≤ N by omega)
  rw [Nat.add_comm] at hn
  subst N
  obtain ⟨i₁,i₂,j₁,j₂,hi,hj,hz₁,hz₂⟩ := hz
  have h := permanent_two_zero_tail_gap (by omega : 25 ≤ n) hD i₁ i₂ j₁ j₂ hi hj hz₁ hz₂
  simpa only [Nat.cast_add,Nat.cast_ofNat,add_sub_cancel_right] using h

/-- The exact finite references for orders 22 through 26 are strict floors. -/
theorem permanent_two_zero_finite_gap {n : ℕ} (hn : 21 ≤ n) (hn' : n ≤ 25)
    {D : Board (n+1) (n+1)} (hD : D ∈ doublyStochastic ℝ (Fin (n+1)))
    (i₁ i₂ j₁ j₂ : Fin (n+1)) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hz₁ : D i₁ j₁ = 0) (hz₂ : D i₂ j₂ = 0) :
    (Certificates.nearEndpointPermanentFloorRat n : ℝ) < D.permanent := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
  rw [Nat.add_comm] at hm
  subst n
  obtain ⟨a,b,ha,haM,hb,hbM,hper⟩ := twoZeroReducedPermanent_representative
    (by omega : 2 ≤ m) hD i₁ i₂ j₁ j₂ hi hj hz₁ hz₂
  have h := nearEndpoint_twoZeroReducedPermanent_finite_lt hn hn' ha hb
    (by simpa using haM) (by simpa using hbM)
  have h' : (Certificates.nearEndpointPermanentFloorRat (m+1) : ℝ) <
      twoZeroReducedPermanent m a b := by simpa using h
  exact h'.trans_le hper

end DittertRybin
