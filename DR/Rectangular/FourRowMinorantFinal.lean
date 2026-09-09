import DR.Rectangular.FourRowMinorantFullFeasible

/-!
# The corrected four-row minorant on both closed probability simplices

The conclusion is the actual leading-kernel quadratic inequality, without
any assumed optimizer shape, stationary feasibility, face reduction, or
polynomial certificate identity. All those inputs are proved in the imported
modules, including the exact repeated-row Bernstein certificate.
-/

namespace DittertRybin
open scoped BigOperators

theorem fourRowMinorantHomogeneous_nonneg (r v : Fin 4 → ℝ)
    (hr : ∀ i,0≤r i) (hsr : ∑ i,r i=1)
    (hv : ∀ i,0≤v i) (hsv : ∑ i,v i=1) :
    0 ≤ fourRowMinorantHomogeneous r v := by
  by_cases hrp : ∀ i,0<r i
  · obtain ⟨u,hu,hmin0⟩ := (isCompact_stdSimplex ℝ (Fin 4)).exists_isMinOn
      ⟨v,hv,hsv⟩ (fourRowMinorantHomogeneous_continuous_right r).continuousOn
    have hmin : IsFourRowMinorantMinimum r u := fun w hw hws => hmin0 ⟨hw,hws⟩
    have hnon : 0 ≤ fourRowMinorantHomogeneous r u := by
      by_cases hup : ∀ i,0<u i
      · have hq := hmin.squareSum_lt hrp hsr hup hu.2
        have heq := hmin.eq_stationary hrp hsr hup hu.2
        rw [heq]
        apply fourRowMinorantStationary_feasible_nonneg r hr hsr hq
        intro i
        rw [←heq]
        exact hu.1 i
      · push Not at hup
        obtain ⟨i,hi⟩ := hup
        exact fourRowMinorantHomogeneous_proper_face_nonneg r u hr hsr hu.1 hu.2
          ⟨i,le_antisymm hi (hu.1 i)⟩
    exact hnon.trans (hmin v hv hsv)
  · push Not at hrp
    obtain ⟨i,hi⟩ := hrp
    exact fourRowMinorantHomogeneous_boundary_nonneg r v hr hsr hv hsv
      ⟨i,le_antisymm hi (hr i)⟩

/-- The corrected four-row minorant, for all nonnegative probability vectors
r and v, including every zero row and every proper or full v support. -/
theorem fourRow_corrected_minorant (r v : Fin 4 → ℝ)
    (hr : ∀ i,0≤r i) (hsr : ∑ i,r i=1)
    (hv : ∀ i,0≤v i) (hsv : ∑ i,v i=1) :
    (∑ i,v i*(1-fourRowGaugeCollision r i)) ≤
      Certificates.quadraticValue (fourRowLeadingKernel r) v := by
  have h := fourRowMinorantHomogeneous_nonneg r v hr hsr hv hsv
  rw [fourRowMinorantHomogeneous_eq_gap r v hsr hsv] at h
  linarith

end DittertRybin
