import DR.Square.CapacityStability
import DR.Square.Permanent
import Mathlib.Data.Finsupp.Fintype

/-!
# The squarefree matrix-product coefficient is the permanent

Expanding the product of row linear forms gives one term for every map
from rows to columns. Its exponent vector counts column occupancies.
The all-one exponent vector forces surjectivity, hence bijectivity on
the finite square index set. This also includes the empty matrix.
-/

namespace DittertRybin

open scoped BigOperators

/-- The squarefree exponent containing every variable once, including the empty vector. -/
noncomputable def squarefreeExponent (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

theorem squarefreeExponent_apply (n : ℕ) (j : Fin n) : squarefreeExponent n j = 1 := by
  simp [squarefreeExponent]

noncomputable def columnOccupancy {n : ℕ} (f : Fin n → Fin n) : Fin n →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

theorem columnOccupancy_eq_squarefree_iff {n : ℕ} (f : Fin n → Fin n) :
    columnOccupancy f = squarefreeExponent n ↔ Function.Bijective f := by
  classical
  constructor
  · intro h
    have hsurj : Function.Surjective f := by
      intro j
      by_contra hj
      have hne : ∀ i, f i ≠ j := by simpa using hj
      have hzero : columnOccupancy f j = 0 := by
        simp [columnOccupancy, hne]
      rw [h, squarefreeExponent_apply] at hzero
      omega
    exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  · intro hf
    let e := Equiv.ofBijective f hf
    have he : columnOccupancy f = ∑ j, Finsupp.single j 1 := by
      change (∑ i, Finsupp.single (f i) 1) = _
      exact Equiv.sum_comp e (fun j : Fin n => Finsupp.single j (1 : ℕ))
    rw [he]
    ext j
    simp [squarefreeExponent_apply, Finsupp.single_apply]

theorem matrixProductPolynomial_function_sum {n : ℕ} (A : Board n n) :
    matrixProductPolynomial A = ∑ f : Fin n → Fin n,
      MvPolynomial.monomial (columnOccupancy f) (∏ i, A i (f i)) := by
  classical
  unfold matrixProductPolynomial
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [columnOccupancy, MvPolynomial.monomial_sum_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [MvPolynomial.X, MvPolynomial.C_mul_monomial]

noncomputable def bijectiveMapsEquivPerm (n : ℕ) :
    {f : Fin n → Fin n // Function.Bijective f} ≃ Equiv.Perm (Fin n) where
  toFun f := Equiv.ofBijective f.val f.property
  invFun e := ⟨e, e.bijective⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv e := by ext i; rfl

/-- The exact coefficient identity required by the permanent-capacity induction. -/
theorem matrixProductPolynomial_squarefree_coefficient {n : ℕ} (A : Board n n) :
    (matrixProductPolynomial A).coeff (squarefreeExponent n) = A.permanent := by
  classical
  rw [matrixProductPolynomial_function_sum]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    columnOccupancy_eq_squarefree_iff]
  rw [← Finset.sum_filter]
  calc
    _ = ∑ f : {f : Fin n → Fin n // Function.Bijective f}, ∏ i, A i (f.val i) := by
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ e : Equiv.Perm (Fin n), ∏ i, A i (e i) := by
      apply Fintype.sum_equiv (bijectiveMapsEquivPerm n)
      intro f
      rfl
    _ = A.permanent := by
      rw [← Matrix.permanent_transpose]
      rfl

end DittertRybin
