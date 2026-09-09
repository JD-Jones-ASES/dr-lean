import DR.Certificates.OrdinaryColumnBlocks
import Mathlib.Tactic.FinCases

open DittertRybin.Certificates
open scoped BigOperators

private def a : Matrix Unit Unit ℝ := fun _ _ => 2
private def g : Matrix Unit Unit ℝ := fun _ _ => -1
private def d : Matrix Unit Unit ℝ := fun _ _ => 2
private def o : Matrix Unit Unit ℝ := fun _ _ => -1
private noncomputable def half : Matrix Unit Unit ℝ := fun _ _ => 1/2

-- The three-cell complete-graph Laplacian has exact signed value 26.
example : quadraticValue (ordinaryColumnMatrix a g d o)
    (Sum.elim (fun _ => 3) (fun q : Fin 2 × Unit => if q.1 = 0 then -1 else 2)) = 26 := by
  rw [quadraticValue_ordinaryColumnMatrix a g d o (fun _ => 3)
    (fun c _ => if c = 0 then -1 else 2)]
  norm_num [quadraticValue, a,g,d,o, Fin.sum_univ_succ]

-- Omitting division by the number of ordinary columns gives the wrong aggregate entry.
example : ordinaryAggregateMatrix a g d o 2 (.inr ()) (.inr ()) ≠
    d () () + (2-1)*o () () := by
  norm_num [ordinaryAggregateMatrix, d,o]

-- The decomposition also covers a single ordinary column, with zero fluctuation.
example (x : Unit → ℝ) (y : Unit → Unit → ℝ) :
    quadraticValue (ordinaryColumnMatrix a g d o) (Sum.elim x (fun q => y q.1 q.2)) =
      quadraticValue (ordinaryAggregateMatrix a g d o 1) (Sum.elim x (y ())) := by
  have h := quadraticValue_ordinaryColumn_decomposition a g d o x y (by norm_num)
  simpa only [Fintype.card_unique, Nat.cast_one, Fintype.sum_unique, div_one,
    sub_self, quadraticValue, zero_mul, mul_zero, Finset.sum_const_zero, add_zero] using h

-- A merely semidefinite fluctuation block cannot prove a one-dimensional full kernel.
example : quadraticValue
    (ordinaryColumnMatrix a g half half)
    (Sum.elim (fun _ => 0) (fun q : Fin 2 × Unit => if q.1 = 0 then -1 else 1)) = 0 := by
  rw [quadraticValue_ordinaryColumnMatrix a g half half (fun _ => 0)
    (fun c _ => if c = 0 then -1 else 1)]
  norm_num [quadraticValue, a,g,half, Fin.sum_univ_succ]

example : ¬ ∃ t : ℝ, ∀ c : Fin 2, (if c = 0 then (-1 : ℝ) else 1) = t := by
  rintro ⟨t,h⟩
  have h0 := h 0
  have h1 := h 1
  norm_num at h0 h1
  linarith

-- Closed statement audit: positivity concerns the actual full matrix, not its definition alone.
example {ι κ γ : Type*} [Fintype ι] [Fintype κ] [Fintype γ] [DecidableEq γ]
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hA : A.IsSymm) (hD : D.IsSymm) (hO : O.IsSymm)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (hB : (ordinaryAggregateMatrix A G D O (Fintype.card γ)).PosSemidef)
    (hH : (D - O).PosSemidef) :
    (ordinaryColumnMatrix (γ := γ) A G D O).PosSemidef :=
  ordinaryColumnMatrix_posSemidef A G D O hA hD hO hell hB hH

#print axioms quadraticValue_ordinaryColumn_decomposition
#print axioms ordinaryColumnMatrix_posSemidef
#print axioms quadraticValue_ordinaryColumn_eq_zero_iff
