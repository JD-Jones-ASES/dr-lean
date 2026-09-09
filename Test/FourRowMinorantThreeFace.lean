import DR.Rectangular.FourRowMinorantThreeFace

namespace DittertRybin.Test.FourRowMinorantThreeFace
open scoped BigOperators

-- The singular D=0 regime is covered on the entire proper v face.
example (v : Fin 4 → ℝ) (hv : ∀ i,0≤v i) (hs : ∑ i,v i=1) (h3 : v 3=0) :
    0 ≤ fourRowMinorantHomogeneous ![4,1,1,1] v :=
  fourRowMinorantHomogeneous_three_face_positive_rows 4 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) v hv hs h3

-- Negative D is covered too, without a stationary-vector feasibility assumption.
example (v : Fin 4 → ℝ) (hv : ∀ i,0≤v i) (hs : ∑ i,v i=1) (h3 : v 3=0) :
    0 ≤ fourRowMinorantHomogeneous ![5,1,1,1] v :=
  fourRowMinorantHomogeneous_three_face_positive_rows 5 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) v hv hs h3

-- The actual corrected kernel inequality on any proper face, with arbitrary zero rows.
example (r v : Fin 4 → ℝ) (hr : ∀ i,0≤r i) (hsr : ∑ i,r i=1)
    (hv : ∀ i,0≤v i) (hsv : ∑ i,v i=1) (hz : v 1=0) :
    (∑ i,v i*(1-fourRowGaugeCollision r i)) ≤
      Certificates.quadraticValue (fourRowLeadingKernel r) v := by
  have h := fourRowMinorantHomogeneous_proper_face_nonneg r v hr hsr hv hsv ⟨1,hz⟩
  rw [fourRowMinorantHomogeneous_eq_gap r v hsr hsv] at h
  linarith

-- Compactness actually supplies both minimization and the maximum-norm tie choice.
example (r : Fin 4 → ℝ) : ∃ v, (∀ i,0≤v i) ∧ (∑ i,v i)=1 ∧ v 3=0 ∧
    IsThreeFaceMinorantMinimum r v ∧ IsThreeFaceMinorantMaxNormTie r v :=
  exists_threeFace_minorant_minimum_max_norm r

#print axioms exists_threeFace_minorant_minimum_max_norm
#print axioms threeFace_line_eventually_feasible
#print axioms IsThreeFaceMinorantMaxNormTie.quadratic_zero
#print axioms fourRowThreeConcentrationDirection_quadratic
#print axioms IsThreeFaceMinorantMinimum.discriminant_pos
#print axioms IsThreeFaceMinorantMinimum.eq_stationary
#print axioms fourRowMinorantHomogeneous_three_face_positive_rows
#print axioms fourRowMinorantHomogeneous_proper_face_nonneg

end DittertRybin.Test.FourRowMinorantThreeFace
