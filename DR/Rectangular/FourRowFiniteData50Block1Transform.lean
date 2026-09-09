import DR.Rectangular.FourRowFiniteData50Block1Checks
import DR.Rectangular.FourRowFiniteDataBernstein

/-! Exact coefficient transformation, including both closed endpoints. -/

namespace DittertRybin
open Certificates

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_0 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 0 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 0 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_1 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 1 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 1 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_2 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 2 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 2 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_3 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 3 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 3 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_4 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 4 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 4 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_5 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 5 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 5 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_6 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 6 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 6 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_7 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 7 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 7 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_8 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 8 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 8 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block1Transform_9 : ∀ i j : Fin 2,
    fourRowFinite50Block1Bernstein 9 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) 9 i j := by
  dsimp only [fourRowFinite50Block1Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

theorem fourRowFinite50Block1Bernstein_eq (k : Fin 10) :
    fourRowFinite50Block1Bernstein k = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite50Block1Power i j k) k := by
  ext i j
  fin_cases k
  · exact fourRowFinite50Block1Transform_0 i j
  · exact fourRowFinite50Block1Transform_1 i j
  · exact fourRowFinite50Block1Transform_2 i j
  · exact fourRowFinite50Block1Transform_3 i j
  · exact fourRowFinite50Block1Transform_4 i j
  · exact fourRowFinite50Block1Transform_5 i j
  · exact fourRowFinite50Block1Transform_6 i j
  · exact fourRowFinite50Block1Transform_7 i j
  · exact fourRowFinite50Block1Transform_8 i j
  · exact fourRowFinite50Block1Transform_9 i j

theorem fourRowFinite50Block1Polynomial_posDef (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) :
    (fourRowFiniteMatrixPolynomial (fun k i j => fourRowFinite50Block1Power i j k) u).PosDef := by
  apply fourRowFiniteMatrixPolynomial_posDef (1/10) 1 _ (by norm_num)
  · intro k
    rw [← fourRowFinite50Block1Bernstein_eq]
    exact fourRowFinite50Block1Bernstein_posDef k
  · norm_num
    exact hu

end DittertRybin
