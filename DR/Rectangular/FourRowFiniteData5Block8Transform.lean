import DR.Rectangular.FourRowFiniteData5Block8Checks
import DR.Rectangular.FourRowFiniteDataBernstein

/-! Exact coefficient transformation, including both closed endpoints. -/

namespace DittertRybin
open Certificates

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_0 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 0 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 0 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_1 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 1 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 1 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_2 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 2 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 2 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_3 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 3 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 3 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_4 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 4 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 4 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_5 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 5 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 5 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_6 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 6 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 6 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_7 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 7 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 7 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_8 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 8 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 8 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block8Transform_9 : ∀ i j : Fin 5,
    fourRowFinite5Block8Bernstein 9 i j = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) 9 i j := by
  dsimp only [fourRowFinite5Block8Bernstein, fourRowFiniteMatrixBernstein]
  simp_rw [fourRowFiniteBernsteinNine_apply]
  decide +kernel

theorem fourRowFinite5Block8Bernstein_eq (k : Fin 10) :
    fourRowFinite5Block8Bernstein k = fourRowFiniteMatrixBernstein (1/10) 1
      (fun k i j => fourRowFinite5Block8Power i j k) k := by
  ext i j
  fin_cases k
  · exact fourRowFinite5Block8Transform_0 i j
  · exact fourRowFinite5Block8Transform_1 i j
  · exact fourRowFinite5Block8Transform_2 i j
  · exact fourRowFinite5Block8Transform_3 i j
  · exact fourRowFinite5Block8Transform_4 i j
  · exact fourRowFinite5Block8Transform_5 i j
  · exact fourRowFinite5Block8Transform_6 i j
  · exact fourRowFinite5Block8Transform_7 i j
  · exact fourRowFinite5Block8Transform_8 i j
  · exact fourRowFinite5Block8Transform_9 i j

theorem fourRowFinite5Block8Polynomial_posDef (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) :
    (fourRowFiniteMatrixPolynomial (fun k i j => fourRowFinite5Block8Power i j k) u).PosDef := by
  apply fourRowFiniteMatrixPolynomial_posDef (1/10) 1 _ (by norm_num)
  · intro k
    rw [← fourRowFinite5Block8Bernstein_eq]
    exact fourRowFinite5Block8Bernstein_posDef k
  · norm_num
    exact hu

end DittertRybin
