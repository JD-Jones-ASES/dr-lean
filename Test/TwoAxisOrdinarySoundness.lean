import DR.Certificates.TwoAxisOrdinaryKernel
import Mathlib.Algebra.Order.Star.Real

namespace DittertRybin.Tests
open Certificates
noncomputable section

private abbrev Compressed := (Fin 0 ⊕ Unit) × (Fin 0 ⊕ Unit)
private def origin : Compressed := (.inr (),.inr ())
private theorem row_eq_origin (p : Fin 0 ⊕ Unit) : p = .inr () := by
  cases p with
  | inl i => exact Fin.elim0 i
  | inr u => cases u; rfl
private theorem compressed_eq_origin (p : Compressed) : p = origin :=
  Prod.ext (row_eq_origin p.1) (row_eq_origin p.2)

private def oneCellKernel : OrdinaryPair (Fin 0) → OrdinaryPair (Fin 0) → ℝ
  | .same,.same => 1
  | .different,.same => 2
  | .same,.different => 2
  | _,_ => 0

private theorem oneCellKernel_symm : TwoAxisOrdinarySymm oneCellKernel := by
  intro r c
  cases r <;> cases c <;> rfl

private theorem oneCell_trivial_psd : (twoAxisTrivialMatrix oneCellKernel 1 1).PosSemidef := by
  have he : twoAxisTrivialMatrix oneCellKernel 1 1 =
      Matrix.vecMulVec (fun _ : Compressed => (1 : ℝ)) (star (fun _ : Compressed => (1 : ℝ))) := by
    ext p q
    rw [compressed_eq_origin p,compressed_eq_origin q]
    norm_num [twoAxisTrivialMatrix,ordinaryPairAverage,oneCellKernel,origin,Matrix.vecMulVec]
  rw [he]
  exact Matrix.posSemidef_vecMulVec_self_star _

-- With both ordinary counts one, negative absent sectors do not obstruct PSD.
example : twoAxisInteraction oneCellKernel = -3 := by
  norm_num [twoAxisInteraction,oneCellKernel]

example : (twoAxisOrdinaryMatrix (ρ := Unit) (γ := Unit) oneCellKernel).PosSemidef := by
  exact twoAxisOrdinaryMatrix_posSemidef oneCellKernel oneCellKernel_symm
    (by norm_num) (by norm_num) (by simpa using oneCell_trivial_psd)
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)

private def oneRowLaplacian : OrdinaryPair (Fin 0) → OrdinaryPair (Fin 0) → ℝ
  | .same,.same => 1
  | .same,.different => -1
  | .different,.same => 10
  | _,_ => 0

private theorem oneRowLaplacian_symm : TwoAxisOrdinarySymm oneRowLaplacian := by
  intro r c
  cases r <;> cases c <;> rfl

private theorem laplacian_trivial_zero : twoAxisTrivialMatrix oneRowLaplacian 1 2 = 0 := by
  ext p q
  rw [compressed_eq_origin p,compressed_eq_origin q]
  norm_num [twoAxisTrivialMatrix,ordinaryPairAverage,oneRowLaplacian,origin]

private theorem laplacian_column_pd : (twoAxisColumnStandardMatrix oneRowLaplacian 1).PosDef := by
  have hs : (twoAxisColumnStandardMatrix oneRowLaplacian 1).IsSymm := by
    apply Matrix.IsSymm.ext
    intro p q
    rw [row_eq_origin p,row_eq_origin q]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hs)
  intro v hv
  have hn : v (.inr ()) ≠ 0 := by
    intro h
    apply hv
    funext p
    rw [row_eq_origin p]
    exact h
  have hp : 0 < 2*(v (.inr ()))^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hn)
  simpa [dotProduct,Matrix.mulVec,twoAxisColumnStandardMatrix,ordinaryPairAverage,
    oneRowLaplacian,Fintype.sum_sum_type,pow_two,mul_assoc,mul_comm,mul_left_comm] using hp

private theorem laplacian_trivial_kernel (z : Compressed → ℝ) :
    quadraticValue (twoAxisTrivialMatrix oneRowLaplacian 1 2) z = 0 ↔
      ∃ t : ℝ, ∀ q, z q = t*twoAxisAggregateWeight 1 2 q := by
  constructor
  · intro _
    refine ⟨z origin/2,?_⟩
    intro q
    rw [compressed_eq_origin q]
    norm_num [origin,twoAxisAggregateWeight,ordinaryAxisWeight]
  · intro _
    simp [laplacian_trivial_zero,quadraticValue]

-- At R=1,C=2 the row sector and interaction are absent and may both be negative.
example : twoAxisRowStandardMatrix oneRowLaplacian 2 (.inr ()) (.inr ()) = -5 ∧
    twoAxisInteraction oneRowLaplacian = -8 := by
  norm_num [twoAxisRowStandardMatrix,ordinaryPairAverage,twoAxisInteraction,oneRowLaplacian]

example (p : (Fin 0 ⊕ Unit) × (Fin 0 ⊕ Fin 2) → ℝ) :
    quadraticValue (twoAxisOrdinaryMatrix oneRowLaplacian) p = 0 ↔ ∃ t : ℝ, ∀ q, p q = t := by
  apply twoAxisOrdinaryMatrix_constant_kernel oneRowLaplacian oneRowLaplacian_symm
    (by norm_num) (by norm_num)
  · simpa only [Fintype.card_unique,Fintype.card_fin,Nat.cast_one,Nat.cast_ofNat,
      laplacian_trivial_zero] using (Matrix.PosSemidef.zero : (0 : Matrix Compressed Compressed ℝ).PosSemidef)
  · exact Or.inl rfl
  · exact Or.inr (by simpa using laplacian_column_pd)
  · exact Or.inl rfl
  · simpa using laplacian_trivial_kernel

-- The aggregate alone cannot replace strict positivity of present standards.
example (z : Compressed → ℝ) :
    quadraticValue (twoAxisTrivialMatrix (fun _ _ => 0) 2 2) z = 0 ↔
      ∃ t : ℝ, ∀ q, z q = t*twoAxisAggregateWeight 2 2 q := by
  constructor
  · intro _
    refine ⟨z origin/4,?_⟩
    intro q
    rw [compressed_eq_origin q]
    norm_num [origin,twoAxisAggregateWeight,ordinaryAxisWeight]
  · intro _
    simp [quadraticValue,twoAxisTrivialMatrix,ordinaryPairAverage,
      Fintype.sum_prod_type,Fintype.sum_sum_type]

private def concentratedVector : (Fin 0 ⊕ Fin 2) × (Fin 0 ⊕ Fin 2) → ℝ :=
  fun p => if p = (.inr 0,.inr 0) then 1 else 0

example : quadraticValue (twoAxisOrdinaryMatrix (fun _ _ => 0)) concentratedVector = 0 ∧
    ¬ ∃ t : ℝ, ∀ q, concentratedVector q = t := by
  constructor
  · simp [quadraticValue,twoAxisOrdinaryMatrix]
  · rintro ⟨t,ht⟩
    have h1 := ht (.inr 0,.inr 0)
    have h0 := ht (.inr 1,.inr 0)
    norm_num [concentratedVector] at h1 h0
    linarith

#print axioms twoAxisOrdinaryMatrix_posSemidef
#print axioms twoAxis_zero_structure
#print axioms twoAxis_constant_of_aggregate_fluctuations
#print axioms twoAxisOrdinaryMatrix_constant_kernel

end
end DittertRybin.Tests
