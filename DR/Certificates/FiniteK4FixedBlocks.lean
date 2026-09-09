import DR.Certificates.FiniteK4FixedRoleLookup
import DR.Rectangular.FourRowFinitePairIndex
import Mathlib.Data.Rat.BigOperators

/-! Formula-defined rational/real sectors for fixed K4 certificates. Ambient
row and column counts are both variable. The compressed index is row-major,
and the principal block deletes only the final ordinary/ordinary coordinate. -/
namespace DittertRybin.Certificates
noncomputable section

section Field
variable {𝕜 : Type*} [Field 𝕜]

def finiteK4FixedAverage {α : Type*} (ell : 𝕜) (f : OrdinaryPair α → 𝕜) :
    Matrix (α ⊕ Unit) (α ⊕ Unit) 𝕜
  | .inl i, .inl j => f (.dist i j)
  | .inl i, .inr _ => f (.toOrdinary i)
  | .inr _, .inl j => f (.fromOrdinary j)
  | .inr _, .inr _ => f .different + (f .same-f .different)/ell

def finiteK4FixedRelation (coeff : Fin 407 → 𝕜) (s : Fin 10)
    (r : OrdinaryPair (Fin (fourRowFiniteSeedRows s)))
    (c : OrdinaryPair (Fin (fourRowFiniteSeedColumns s))) : 𝕜 :=
  coeff (finiteK4FixedRoleLookup (fourRowFiniteSeedPairKey s r c))

def finiteK4FixedFullMatrix (coeff : Fin 407 → 𝕜) (m n : ℕ) (s : Fin 10) :
    Matrix (Fin (fourRowFiniteSeedFullSize s)) (Fin (fourRowFiniteSeedFullSize s)) 𝕜 :=
  fun i j =>
    let p := (fourRowFiniteSeedCompressedEquiv s).symm i
    let q := (fourRowFiniteSeedCompressedEquiv s).symm j
    finiteK4FixedAverage ((m-fourRowFiniteSeedRows s : ℕ) : 𝕜)
      (fun r => finiteK4FixedAverage ((n-fourRowFiniteSeedColumns s : ℕ) : 𝕜)
        (finiteK4FixedRelation coeff s r) p.2 q.2) p.1 q.1

def finiteK4FixedPrincipalMatrix (coeff : Fin 407 → 𝕜) (m n : ℕ) (s : Fin 10) :
    Matrix (Fin (fourRowFiniteSeedFullSize s-1)) (Fin (fourRowFiniteSeedFullSize s-1)) 𝕜 :=
  (finiteK4FixedFullMatrix coeff m n s).submatrix
    (Fin.castLE (Nat.sub_le _ 1)) (Fin.castLE (Nat.sub_le _ 1))

def finiteK4FixedRowMatrix (coeff : Fin 407 → 𝕜) (n : ℕ) (s : Fin 10) :
    Matrix (Fin (fourRowFiniteSeedColumns s+1)) (Fin (fourRowFiniteSeedColumns s+1)) 𝕜 :=
  fun i j => finiteK4FixedAverage ((n-fourRowFiniteSeedColumns s : ℕ) : 𝕜)
    (fun c => finiteK4FixedRelation coeff s .same c-finiteK4FixedRelation coeff s .different c)
    ((fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s)).symm i)
    ((fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s)).symm j)

def finiteK4FixedColumnMatrix (coeff : Fin 407 → 𝕜) (m : ℕ) (s : Fin 10) :
    Matrix (Fin (fourRowFiniteSeedRows s+1)) (Fin (fourRowFiniteSeedRows s+1)) 𝕜 :=
  fun i j => finiteK4FixedAverage ((m-fourRowFiniteSeedRows s : ℕ) : 𝕜)
    (fun r => finiteK4FixedRelation coeff s r .same-finiteK4FixedRelation coeff s r .different)
    ((fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s)).symm i)
    ((fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s)).symm j)

def finiteK4FixedInteractionMatrix (coeff : Fin 407 → 𝕜) (s : Fin 10) :
    Matrix (Fin 1) (Fin 1) 𝕜 :=
  fun _ _ => finiteK4FixedRelation coeff s .same .same-
    finiteK4FixedRelation coeff s .different .same-finiteK4FixedRelation coeff s .same .different+
      finiteK4FixedRelation coeff s .different .different

def finiteK4FixedAxisWeight {α : Type*} (count : 𝕜) : α ⊕ Unit → 𝕜
  | .inl _ => 1
  | .inr _ => count

def finiteK4FixedWeight (m n : ℕ) (s : Fin 10)
    (i : Fin (fourRowFiniteSeedFullSize s)) : 𝕜 :=
  let p := (fourRowFiniteSeedCompressedEquiv s).symm i
  finiteK4FixedAxisWeight ((m-fourRowFiniteSeedRows s : ℕ) : 𝕜) p.1 *
    finiteK4FixedAxisWeight ((n-fourRowFiniteSeedColumns s : ℕ) : 𝕜) p.2

end Field

theorem finiteK4FixedAverage_cast {α : Type*} (ell : ℚ) (f : OrdinaryPair α → ℚ)
    (i j : α ⊕ Unit) :
    ((finiteK4FixedAverage ell f i j : ℚ) : ℝ) =
      finiteK4FixedAverage (ell : ℝ) (fun r => (f r : ℝ)) i j := by
  cases i <;> cases j <;> simp [finiteK4FixedAverage]

theorem finiteK4FixedFullMatrix_cast (coeff : Fin 407 → ℚ) (m n : ℕ) (s : Fin 10) :
    (finiteK4FixedFullMatrix coeff m n s).map (fun q : ℚ => (q : ℝ)) =
      finiteK4FixedFullMatrix (fun k => (coeff k : ℝ)) m n s := by
  ext i j
  simp only [Matrix.map_apply,finiteK4FixedFullMatrix,finiteK4FixedAverage_cast,
    Rat.cast_natCast,finiteK4FixedRelation]
  rfl

theorem finiteK4FixedPrincipalMatrix_cast (coeff : Fin 407 → ℚ) (m n : ℕ) (s : Fin 10) :
    (finiteK4FixedPrincipalMatrix coeff m n s).map (fun q : ℚ => (q : ℝ)) =
      finiteK4FixedPrincipalMatrix (fun k => (coeff k : ℝ)) m n s := by
  exact congrArg (fun Q => Q.submatrix (Fin.castLE (Nat.sub_le (fourRowFiniteSeedFullSize s) 1))
    (Fin.castLE (Nat.sub_le (fourRowFiniteSeedFullSize s) 1)))
    (finiteK4FixedFullMatrix_cast coeff m n s)

theorem finiteK4FixedRowMatrix_cast (coeff : Fin 407 → ℚ) (n : ℕ) (s : Fin 10) :
    (finiteK4FixedRowMatrix coeff n s).map (fun q : ℚ => (q : ℝ)) =
      finiteK4FixedRowMatrix (fun k => (coeff k : ℝ)) n s := by
  ext i j
  simp only [Matrix.map_apply,finiteK4FixedRowMatrix,finiteK4FixedAverage_cast,
    Rat.cast_natCast,Rat.cast_sub,finiteK4FixedRelation]

theorem finiteK4FixedColumnMatrix_cast (coeff : Fin 407 → ℚ) (m : ℕ) (s : Fin 10) :
    (finiteK4FixedColumnMatrix coeff m s).map (fun q : ℚ => (q : ℝ)) =
      finiteK4FixedColumnMatrix (fun k => (coeff k : ℝ)) m s := by
  ext i j
  simp only [Matrix.map_apply,finiteK4FixedColumnMatrix,finiteK4FixedAverage_cast,
    Rat.cast_natCast,Rat.cast_sub,finiteK4FixedRelation]

theorem finiteK4FixedInteractionMatrix_cast (coeff : Fin 407 → ℚ) (s : Fin 10) :
    (finiteK4FixedInteractionMatrix coeff s).map (fun q : ℚ => (q : ℝ)) =
      finiteK4FixedInteractionMatrix (fun k => (coeff k : ℝ)) s := by
  ext i j
  simp only [Matrix.map_apply,finiteK4FixedInteractionMatrix,Rat.cast_sub,Rat.cast_add,
    finiteK4FixedRelation]

theorem finiteK4FixedAxisWeight_cast {α : Type*} (count : ℚ) (p : α ⊕ Unit) :
    ((finiteK4FixedAxisWeight count p : ℚ) : ℝ) = finiteK4FixedAxisWeight (count : ℝ) p := by
  cases p <;> simp [finiteK4FixedAxisWeight]

theorem finiteK4FixedWeight_cast (m n : ℕ) (s : Fin 10)
    (i : Fin (fourRowFiniteSeedFullSize s)) :
    ((finiteK4FixedWeight m n s i : ℚ) : ℝ) = finiteK4FixedWeight m n s i := by
  simp only [finiteK4FixedWeight,Rat.cast_mul,finiteK4FixedAxisWeight_cast,Rat.cast_natCast]

theorem finiteK4FixedFullMatrix_reindex (coeff : Fin 407 → ℝ) (m n : ℕ) (s : Fin 10) :
    (finiteK4FixedFullMatrix coeff m n s).submatrix
      (fourRowFiniteSeedCompressedEquiv s) (fourRowFiniteSeedCompressedEquiv s) =
      twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s (fun key => coeff (finiteK4FixedRoleLookup key)))
        (m-fourRowFiniteSeedRows s : ℕ) (n-fourRowFiniteSeedColumns s : ℕ) := by
  ext p q
  simp only [Matrix.submatrix_apply,finiteK4FixedFullMatrix,Equiv.symm_apply_apply]
  rfl

theorem finiteK4FixedRowMatrix_reindex (coeff : Fin 407 → ℝ) (n : ℕ) (s : Fin 10) :
    (finiteK4FixedRowMatrix coeff n s).submatrix
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s))
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s)) =
      twoAxisRowStandardMatrix
        (fourRowFiniteSeedRelationKernel s (fun key => coeff (finiteK4FixedRoleLookup key)))
        (n-fourRowFiniteSeedColumns s : ℕ) := by
  ext p q
  simp only [Matrix.submatrix_apply,finiteK4FixedRowMatrix,Equiv.symm_apply_apply]
  rfl

theorem finiteK4FixedColumnMatrix_reindex (coeff : Fin 407 → ℝ) (m : ℕ) (s : Fin 10) :
    (finiteK4FixedColumnMatrix coeff m s).submatrix
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s))
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s)) =
      twoAxisColumnStandardMatrix
        (fourRowFiniteSeedRelationKernel s (fun key => coeff (finiteK4FixedRoleLookup key)))
        (m-fourRowFiniteSeedRows s : ℕ) := by
  ext p q
  simp only [Matrix.submatrix_apply,finiteK4FixedColumnMatrix,Equiv.symm_apply_apply]
  rfl

theorem finiteK4FixedInteractionMatrix_eq (coeff : Fin 407 → ℝ) (s : Fin 10) :
    finiteK4FixedInteractionMatrix coeff s 0 0 = twoAxisInteraction
      (fourRowFiniteSeedRelationKernel s (fun key => coeff (finiteK4FixedRoleLookup key))) := rfl

theorem finiteK4FixedWeight_reindex (m n : ℕ) (s : Fin 10)
    (p : (Fin (fourRowFiniteSeedRows s) ⊕ Unit) × (Fin (fourRowFiniteSeedColumns s) ⊕ Unit)) :
    (finiteK4FixedWeight m n s (fourRowFiniteSeedCompressedEquiv s p) : ℝ) =
      twoAxisAggregateWeight (m-fourRowFiniteSeedRows s : ℕ) (n-fourRowFiniteSeedColumns s : ℕ) p := by
  simp only [finiteK4FixedWeight,Equiv.symm_apply_apply]
  rfl

end
end DittertRybin.Certificates
