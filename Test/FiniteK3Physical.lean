import DR.Certificates.FiniteK3Physical
import DR.Certificates.FiniteK3Pairs
import Mathlib.Algebra.Order.Star.Real

open scoped BigOperators
open DittertRybin.Certificates

-- This actual role assignment produces the three-cell star-Laplacian seed.
-- It tests the block criterion independently of quartic coefficient equations.
private def starCoefficient (i : Fin 93) : ℚ :=
  if i = 0 then 2 else if i = 1 then -1 else if i = 4 then 1 else 0

private def mark : Fin 1 × Fin 1 := (0,0)

private theorem starH : finiteK3OrdinaryH starCoefficient mark mark =
    (![![1]] : Matrix (Fin 1) (Fin 1) ℚ) := by
  ext i j
  fin_cases i
  fin_cases j
  decide +kernel
private theorem starB : finiteK3OrdinaryBFlat starCoefficient mark mark 2 =
    (![![2,-1],![-1,1/2]] : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel
private theorem starB0 : finiteK3OrdinaryB0 starCoefficient mark mark 2 =
    (![![2]] : Matrix (Fin 1) (Fin 1) ℚ) := by
  ext i j
  fin_cases i
  fin_cases j
  decide +kernel

private theorem scalar_posDef (a : ℝ) (ha : 0 < a) :
    Matrix.PosDef (![![a]] : Matrix (Fin 1) (Fin 1) ℝ) := by
  have h := Matrix.PosDef.diagonal (fun _ : Fin 1 => ha)
  have heq : (![![a]] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal (fun _ : Fin 1 => a) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.diagonal]
  rw [heq]
  exact h

private theorem star_kernel : ∀ i,
    (∑ j, finiteK3OrdinaryBFlat starCoefficient mark mark (2 : ℚ) i j *
      finiteK3AggregateKernelFlat 1 1 (2 : ℚ) j) = 0 := by
  rw [starB]
  decide +kernel

private theorem star_hH :
    ((finiteK3OrdinaryH starCoefficient mark mark).map (fun q : ℚ => (q : ℝ))).PosDef := by
  rw [starH]
  have heq : Matrix.map (![![1]] : Matrix (Fin 1) (Fin 1) ℚ) (fun q : ℚ => (q : ℝ)) =
      (![![1]] : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    change ((1 : ℚ) : ℝ) = 1
    norm_num
  rw [heq]
  exact scalar_posDef 1 (by norm_num)

private theorem star_hB0 :
    ((finiteK3OrdinaryB0 starCoefficient mark mark (2 : ℚ)).map (fun q : ℚ => (q : ℝ))).PosDef := by
  rw [starB0]
  have heq : Matrix.map (![![2]] : Matrix (Fin 1) (Fin 1) ℚ) (fun q : ℚ => (q : ℝ)) =
      (![![2]] : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    change ((2 : ℚ) : ℝ) = 2
    norm_num
  rw [heq]
  exact scalar_posDef 2 (by norm_num)

-- The full physical seed has exactly the constant quadratic kernel, not merely PSD.
example :
    Matrix.PosSemidef (finiteK3Entry (fun i => (starCoefficient i : ℝ))
      ((0,0) : Fin 1 × Fin 3) (0,0)) ∧
    ∀ p : Fin 1 × Fin 3 → ℝ,
      quadraticValue (finiteK3Entry (fun i => (starCoefficient i : ℝ)) (0,0) (0,0)) p = 0 ↔
        ∃ t : ℝ, ∀ a, p a = t := by
  exact finiteK3Ordinary_rational_rectangle_criterion (by decide : 0 < 1)
    (by decide : 1 < 3) starCoefficient mark mark star_kernel star_hB0 star_hH

-- Replacing ell by one destroys the actual aggregate kernel equation.
example : ¬∀ i,
    (∑ j, finiteK3OrdinaryBFlat starCoefficient mark mark (1 : ℚ) i j *
      finiteK3AggregateKernelFlat 1 1 (1 : ℚ) j) = 0 := by decide +kernel

-- Row and column roles remain distinct in the four representative types.
example : finiteK3MultiplierPairType ((0,0) : Fin 3 × Fin 3) (0,1) = 1 := rfl
example : finiteK3MultiplierPairType ((0,0) : Fin 3 × Fin 3) (1,0) = 2 := rfl
example : finiteK3MultiplierPairType ((2,1) : Fin 3 × Fin 3) (0,2) = 3 := rfl

#print axioms finiteK3Ordinary_kernel_criterion
#print axioms finiteK3Ordinary_flat_criterion
#print axioms finiteK3Ordinary_rational_rectangle_criterion
#print axioms finiteK3_allPairs_of_fourRepresentatives
