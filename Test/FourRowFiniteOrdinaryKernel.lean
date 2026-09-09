import DR.Rectangular.FourRowFiniteOrdinaryKernel
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.Star.Real

namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section

example (y : Fin 1 → Fin 3 → ℝ) :
    (fun i => y 0 i-(∑ c, y c i)/(Fintype.card (Fin 1) : ℝ)) = 0 :=
  ordinaryColumn_fluctuation_eq_zero_of_card_one rfl y 0

private def ordinaryUnitO : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 2

private theorem ordinaryUnitAggregate :
    ordinaryAggregateMatrix (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 1 ordinaryUnitO 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ordinaryAggregateMatrix, ordinaryUnitO, Matrix.one_apply] <;> decide

-- The physical matrix is strictly positive although its absent standard block is negative.
example :
    (ordinaryColumnMatrix (γ := Fin 1) (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 1
      ordinaryUnitO).PosDef := by
  apply ordinaryColumnMatrix_posDef_of_card_one_or
    _ _ _ _ Matrix.isSymm_one Matrix.isSymm_one
    (by apply Matrix.IsSymm.ext; intros; rfl) (by norm_num)
  · simpa only [Fintype.card_fin, Nat.cast_one, ordinaryUnitAggregate] using
      (Matrix.PosDef.one : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).PosDef)
  · exact Or.inl rfl

example : ¬ ((1 : Matrix (Fin 1) (Fin 1) ℝ)-ordinaryUnitO).PosSemidef := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg (fun _ => 1)
  norm_num [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.one_apply, ordinaryUnitO,
    Fin.sum_univ_succ] at hn

-- The weighted-kernel interface permits both zero and negative coordinate weights.
example {ι κ γ : Type*} [Fintype ι] [Fintype κ] [Fintype γ] [DecidableEq γ]
    (A : Matrix ι ι ℝ) (G : Matrix ι κ ℝ) (D O : Matrix κ κ ℝ)
    (hell : (Fintype.card γ : ℝ) ≠ 0)
    (hB : (ordinaryAggregateMatrix A G D O (Fintype.card γ)).PosSemidef)
    (hH : Fintype.card γ = 1 ∨ (D-O).PosDef)
    (hker : ∀ x : ι → ℝ, ∀ z : κ → ℝ,
      quadraticValue (ordinaryAggregateMatrix A G D O (Fintype.card γ)) (Sum.elim x z) = 0 ↔
        ∃ t : ℝ, (∀ i, x i = t*0) ∧ ∀ j, z j = Fintype.card γ*(t*(-3)))
    (x : ι → ℝ) (y : γ → κ → ℝ) :
    quadraticValue (ordinaryColumnMatrix A G D O) (Sum.elim x (fun q => y q.1 q.2)) = 0 ↔
      ∃ t : ℝ, (∀ i, x i = t*0) ∧ ∀ c j, y c j = t*(-3) :=
  quadraticValue_ordinaryColumn_weighted_kernel A G D O hell hB hH
    (fun _ => 0) (fun _ => -3) hker x y

#print axioms ordinaryColumn_fluctuation_eq_zero_of_card_one
#print axioms ordinaryColumnMatrix_posSemidef_of_card_one_or
#print axioms quadraticValue_ordinaryColumn_weighted_kernel
#print axioms ordinaryColumnMatrix_posDef_of_card_one_or

end
end DittertRybin.Certificates
