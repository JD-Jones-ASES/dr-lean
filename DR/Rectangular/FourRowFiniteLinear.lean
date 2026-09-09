import DR.Rectangular.FourRowFiniteBernstein

/-! The exact scalar obligations of the two four-row quintic families.
Coverage by physical samples and matrix rows is separate from these identities. -/

namespace DittertRybin
open scoped BigOperators
noncomputable section

structure FourRowFiniteCoefficientRow where
  terms : List (Fin 391 × ℕ)
  multiplicity : ℕ
  successes : ℕ
  deriving Inhabited

structure FourRowFiniteKernelTerm where
  role : Fin 391
  slope : ℤ
  offset : ℤ

def fourRowFiniteNumeratorExtend (h : Fin 391 → Fin 5 → ℚ)
    (i : Fin 391) (d : ℕ) : ℚ :=
  if hd : d < 5 then h i ⟨d,hd⟩ else 0

/-- The coefficients of `u*(multiplicity*F4(U_(4,a/u))-successes)`. -/
def fourRowFiniteCoefficientRhs (a : ℕ) (row : FourRowFiniteCoefficientRow) : Fin 5 → ℚ :=
  ![0, (row.multiplicity : ℚ)-row.successes,
    -(row.multiplicity : ℚ)*87/(16*a),
    (row.multiplicity : ℚ)*319/(32*a^2),
    -(row.multiplicity : ℚ)*87/(16*a^3)]

def FourRowFiniteCoefficientRow.Valid (row : FourRowFiniteCoefficientRow)
    (a : ℕ) (h : Fin 391 → Fin 5 → ℚ) : Prop :=
  ∀ d : Fin 5, (row.terms.map (fun t => (t.2 : ℚ)*h t.1 d)).sum =
    fourRowFiniteCoefficientRhs a row d

instance (row : FourRowFiniteCoefficientRow) (a : ℕ) (h : Fin 391 → Fin 5 → ℚ) :
    Decidable (row.Valid a h) := by
  unfold FourRowFiniteCoefficientRow.Valid
  infer_instance

def fourRowFiniteKernelValid (row : List FourRowFiniteKernelTerm)
    (a : ℕ) (h : Fin 391 → Fin 5 → ℚ) : Prop :=
  ∀ d : Fin 6, (row.map (fun t =>
    (a : ℚ)*t.slope*fourRowFiniteNumeratorExtend h t.role d +
      if (d : ℕ) = 0 then 0 else (t.offset : ℚ)*fourRowFiniteNumeratorExtend h t.role (d-1))).sum = 0

instance (row : List FourRowFiniteKernelTerm) (a : ℕ) (h : Fin 391 → Fin 5 → ℚ) :
    Decidable (fourRowFiniteKernelValid row a h) := by
  unfold fourRowFiniteKernelValid
  infer_instance

end
end DittertRybin
