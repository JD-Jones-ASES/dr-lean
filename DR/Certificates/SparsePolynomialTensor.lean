import DR.Certificates.SparsePolynomial

/-! Finite coefficient tensors as normalized sparse polynomials, including empty dimensions. -/
namespace DittertRybin.Certificates.SparsePolynomial
noncomputable section
open scoped BigOperators

def polynomialSum (p : List Polynomial) : Polynomial := p.foldr add []

theorem value_polynomialSum {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (p : List Polynomial) :
    value x (polynomialSum p) = (p.map (value x)).sum := by
  induction p with
  | nil => simp [polynomialSum, value]
  | cons q p ih =>
      simp only [polynomialSum, List.foldr_cons, value_add]
      rw [← polynomialSum, ih]
      simp

theorem value_polynomialSum_ofFn {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) {n : ℕ} (p : Fin n → Polynomial) :
    value x (polynomialSum (List.ofFn p)) = ∑ i, value x (p i) := by
  rw [value_polynomialSum, List.map_ofFn, List.sum_ofFn]
  rfl

def fromTensor {a b c : ℕ} (p : Fin a → Fin b → Fin c → ℚ) : Polynomial :=
  polynomialSum (List.ofFn fun i => polynomialSum (List.ofFn fun j =>
    polynomialSum (List.ofFn fun k => [(((k : ℕ), (i : ℕ), (j : ℕ)),p i j k)])))

theorem value_fromTensor {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) {a b c : ℕ} (p : Fin a → Fin b → Fin c → ℚ) :
    value x (fromTensor p) =
      ∑ i, ∑ j, ∑ k, algebraMap ℚ R (p i j k) *
        x 0 ^ (k : ℕ) * x 1 ^ (i : ℕ) * x 2 ^ (j : ℕ) := by
  simp only [fromTensor, value_polynomialSum_ofFn]
  simp [value, termValue, monomial, mul_assoc]

end
end DittertRybin.Certificates.SparsePolynomial
