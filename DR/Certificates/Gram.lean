import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Exact rational Gram certificates

The certificate data are diagonal rational weights and a rational rectangular
factor. Checking a rational entry identity is enough to transfer the resulting
sum of squares to every real vector. Zero weights and singular factors are
allowed. Positive definiteness requires a separate injectivity witness.

This is the matrix soundness layer for the cubic/quartic K=3
certificates and the shifted 16-by-16 seeds of the sextic square-order-four
certificate. Polynomial identities and permutation-orbit coverage remain
separate obligations; a positive Gram matrix alone does not prove P2.
-/

namespace DittertRybin.Certificates

open scoped BigOperators

/-- The ordinary real quadratic value, with off-diagonal entries counted twice. -/
def quadraticValue {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * Q i j * x j

/-- A weighted Gram matrix; transposing a lower LDL factor gives this convention. -/
def weightedGram {R ι κ : Type*} [CommSemiring R] [Fintype κ]
    (d : κ → R) (B : Matrix κ ι R) : Matrix ι ι R :=
  fun i j => ∑ a, d a * B a i * B a j

theorem weightedGram_symmetric {R ι κ : Type*} [CommSemiring R] [Fintype κ]
    (d : κ → R) (B : Matrix κ ι R) (i j : ι) :
    weightedGram d B i j = weightedGram d B j i := by
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The finite Gram identity is an exact sum of weighted real squares. -/
theorem quadraticValue_weightedGram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : κ → ℝ) (B : Matrix κ ι ℝ) (x : ι → ℝ) :
    quadraticValue (weightedGram d B) x = ∑ a, d a * (∑ i, B a i * x i) ^ 2 := by
  unfold quadraticValue weightedGram
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a, ∑ j, x i * (d a * B a i * B a j) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, x i * (d a * B a i * B a j) * x j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [pow_two, Finset.mul_sum]
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem quadraticValue_weightedGram_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : κ → ℝ) (B : Matrix κ ι ℝ) (hd : ∀ a, 0 ≤ d a) (x : ι → ℝ) :
    0 ≤ quadraticValue (weightedGram d B) x := by
  rw [quadraticValue_weightedGram]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hd a) (sq_nonneg _)

theorem weightedGram_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : κ → ℝ) (B : Matrix κ ι ℝ) (hd : ∀ a, 0 ≤ d a) :
    (weightedGram d B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    exact weightedGram_symmetric d B j i
  · intro x
    simpa [quadraticValue, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
      quadraticValue_weightedGram_nonneg d B hd x

/-- Positive weights make the quadratic kernel exactly the kernel of the factor. -/
theorem quadraticValue_weightedGram_eq_zero_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : κ → ℝ) (B : Matrix κ ι ℝ) (hd : ∀ a, 0 < d a) (x : ι → ℝ) :
    quadraticValue (weightedGram d B) x = 0 ↔ ∀ a, (∑ i, B a i * x i) = 0 := by
  rw [quadraticValue_weightedGram]
  constructor
  · intro h a
    have ha : d a * (∑ i, B a i * x i) ^ 2 ≤ 0 := by
      calc
        _ ≤ ∑ b, d b * (∑ i, B b i * x i) ^ 2 :=
          Finset.single_le_sum (fun b _ => mul_nonneg (hd b).le (sq_nonneg _)) (Finset.mem_univ a)
        _ = 0 := h
    exact sq_eq_zero_iff.mp (le_antisymm (nonpos_of_mul_nonpos_right ha (hd a)) (sq_nonneg _))
  · intro h
    simp [h]

theorem weightedGram_posDef_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : κ → ℝ) (B : Matrix κ ι ℝ) (hd : ∀ a, 0 < d a)
    (hB : Function.Injective B.mulVec) : (weightedGram d B).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (weightedGram_posSemidef d B (fun a => (hd a).le)).1
  intro x hx
  have hnonneg := quadraticValue_weightedGram_nonneg d B (fun a => (hd a).le) x
  have hne : quadraticValue (weightedGram d B) x ≠ 0 := by
    intro hzero
    have hall := (quadraticValue_weightedGram_eq_zero_iff d B hd x).mp hzero
    apply hx
    apply hB
    ext a
    simpa [Matrix.mulVec, dotProduct] using hall a
  simpa [quadraticValue, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
    lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Finite rational data; validity is a separately checkable exact arithmetic proposition. -/
structure GramCertificate (n r : ℕ) where
  weights : Fin r → ℚ
  factor : Fin r → Fin n → ℚ

namespace GramCertificate

/-- Only rational inequalities and a rational matrix identity are checked. -/
def Valid {n r : ℕ} (C : GramCertificate n r) (Q : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  (∀ a, 0 ≤ C.weights a) ∧ ∀ i j, Q i j = weightedGram C.weights C.factor i j

instance {n r : ℕ} (C : GramCertificate n r) (Q : Matrix (Fin n) (Fin n) ℚ) :
    Decidable (C.Valid Q) := by
  unfold Valid weightedGram Matrix at *
  infer_instance

/-- Checking the rational factor identity yields the corresponding real entry identity. -/
theorem real_identity {n r : ℕ} (C : GramCertificate n r)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hC : C.Valid Q) :
    (Q.map (fun q : ℚ => (q : ℝ))) =
      weightedGram (fun a => (C.weights a : ℝ)) (fun a i => (C.factor a i : ℝ)) := by
  ext i j
  have h := hC.2 i j
  unfold weightedGram at h ⊢
  have hc := congrArg (fun q : ℚ => (q : ℝ)) h
  simpa only [Rat.cast_sum, Rat.cast_mul, Matrix.map_apply] using hc

theorem quadratic_identity {n r : ℕ} (C : GramCertificate n r)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hC : C.Valid Q) (x : Fin n → ℝ) :
    quadraticValue (Q.map (fun q : ℚ => (q : ℝ))) x =
      ∑ a, (C.weights a : ℝ) * (∑ i, (C.factor a i : ℝ) * x i) ^ 2 := by
  rw [C.real_identity Q hC]
  exact quadraticValue_weightedGram _ _ x

theorem nonneg {n r : ℕ} (C : GramCertificate n r)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hC : C.Valid Q) (x : Fin n → ℝ) :
    0 ≤ quadraticValue (Q.map (fun q : ℚ => (q : ℝ))) x := by
  rw [C.real_identity Q hC]
  exact quadraticValue_weightedGram_nonneg _ _ (fun a => by exact_mod_cast hC.1 a) x

theorem posSemidef {n r : ℕ} (C : GramCertificate n r)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hC : C.Valid Q) :
    (Q.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  rw [C.real_identity Q hC]
  exact weightedGram_posSemidef _ _ (fun a => by exact_mod_cast hC.1 a)

/-- A rational LDL factor uses rows of L-transpose as its Gram factors. -/
def ofLDL {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) : GramCertificate n n :=
  ⟨d, L.transpose⟩

theorem ofLDL_valid {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hd : ∀ a, 0 ≤ d a)
    (hQ : ∀ i j, Q i j = ∑ a, L i a * d a * L j a) : (ofLDL L d).Valid Q := by
  refine ⟨hd, fun i j => ?_⟩
  rw [hQ]
  apply Finset.sum_congr rfl
  intro a _
  dsimp [ofLDL, weightedGram, Matrix.transpose]
  ring

/-- Strict LDL soundness needs exactly positive pivots and a triangular factor with nonzero diagonal. -/
theorem ofLDL_posDef {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hd : ∀ a, 0 < d a)
    (hQ : ∀ i j, Q i j = ∑ a, L i a * d a * L j a)
    (htri : ∀ i j, i < j → L i j = 0) (hdiag : ∀ i, L i i ≠ 0) :
    (Q.map (fun q : ℚ => (q : ℝ))).PosDef := by
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun a i => (L i a : ℝ))
  have hBtri : B.IsUpperTriangular := by
    intro i j hij
    change (L j i : ℝ) = 0
    exact_mod_cast htri j i hij
  have hBdet : B.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hBtri]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    change (L i i : ℝ) ≠ 0
    exact_mod_cast hdiag i
  have hB : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_iff_isUnit_det B |>.mpr (isUnit_iff_ne_zero.mpr hBdet))
  have hC := ofLDL_valid L d Q (fun a => (hd a).le) hQ
  rw [(ofLDL L d).real_identity Q hC]
  exact weightedGram_posDef_of_injective _ B (fun a => by exact_mod_cast hd a) hB

end GramCertificate

/-- Compatibility with Mathlib's matrix positivity interface. -/
theorem quadraticValue_eq_dotProduct {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (x : ι → ℝ) : quadraticValue Q x = x ⬝ᵥ Q.mulVec x := by
  simp [quadraticValue, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- Moving along a known kernel vector preserves the quadratic value. -/
theorem quadraticValue_sub_smul_kernel {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm) (v : ι → ℝ) (hv : Q.mulVec v = 0)
    (x : ι → ℝ) (c : ℝ) : quadraticValue Q (x - c • v) = quadraticValue Q x := by
  have hleft : Matrix.vecMul v Q = 0 := by
    rw [← Matrix.mulVec_transpose, hQ]
    exact hv
  have hcross : v ⬝ᵥ Q.mulVec x = 0 := by
    rw [Matrix.dotProduct_mulVec, hleft, zero_dotProduct]
  rw [quadraticValue_eq_dotProduct, Matrix.mulVec_sub, Matrix.mulVec_smul,
    hv, smul_zero, sub_zero, sub_dotProduct, smul_dotProduct, hcross, smul_zero,
    sub_zero, quadraticValue_eq_dotProduct]

/-- A vector whose final coordinate vanishes has the principal-block quadratic value. -/
theorem quadraticValue_eq_principal_of_last_zero {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Fin (n + 1) → ℝ)
    (hx : x (Fin.last n) = 0) :
    quadraticValue Q x =
      quadraticValue (Q.submatrix Fin.castSucc Fin.castSucc) (fun i => x i.castSucc) := by
  unfold quadraticValue
  rw [Fin.sum_univ_castSucc]
  simp only [hx, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_castSucc]
  simp [hx]

/-- The full matrix is PSD when a principal block is PSD and the omitted direction is a known kernel. -/
theorem posSemidef_of_principal_kernel {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : Q.IsSymm)
    (v : Fin (n + 1) → ℝ) (hv : Q.mulVec v = 0) (hvlast : v (Fin.last n) ≠ 0)
    (hprincipal : (Q.submatrix Fin.castSucc Fin.castSucc).PosSemidef) : Q.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr hQ)
  intro x
  let c := x (Fin.last n) / v (Fin.last n)
  let y := x - c • v
  have hylast : y (Fin.last n) = 0 := by
    change x (Fin.last n) - x (Fin.last n) / v (Fin.last n) * v (Fin.last n) = 0
    field_simp
    ring
  have hvalue : quadraticValue Q x =
      quadraticValue (Q.submatrix Fin.castSucc Fin.castSucc) (fun i => y i.castSucc) :=
    (quadraticValue_sub_smul_kernel Q hQ v hv x c).symm.trans
      (quadraticValue_eq_principal_of_last_zero Q y hylast)
  simp only [star_trivial]
  rw [← quadraticValue_eq_dotProduct, hvalue, quadraticValue_eq_dotProduct]
  simpa using hprincipal.dotProduct_mulVec_nonneg (fun i => y i.castSucc)

/-- A positive principal block gives the exact one-dimensional quadratic kernel. -/
theorem quadraticValue_eq_zero_iff_span_kernel {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : Q.IsSymm)
    (v : Fin (n + 1) → ℝ) (hv : Q.mulVec v = 0) (hvlast : v (Fin.last n) ≠ 0)
    (hprincipal : (Q.submatrix Fin.castSucc Fin.castSucc).PosDef) (x : Fin (n + 1) → ℝ) :
    quadraticValue Q x = 0 ↔ ∃ c : ℝ, x = c • v := by
  constructor
  · intro hx
    let c := x (Fin.last n) / v (Fin.last n)
    let y := x - c • v
    have hylast : y (Fin.last n) = 0 := by
      change x (Fin.last n) - x (Fin.last n) / v (Fin.last n) * v (Fin.last n) = 0
      field_simp
      ring
    have hyvalue : quadraticValue (Q.submatrix Fin.castSucc Fin.castSucc)
        (fun i => y i.castSucc) = 0 := by
      rw [← quadraticValue_eq_principal_of_last_zero Q y hylast]
      exact (quadraticValue_sub_smul_kernel Q hQ v hv x c).trans hx
    have hycast : (fun i : Fin n => y i.castSucc) = 0 := by
      by_contra hn
      have hpos := hprincipal.dotProduct_mulVec_pos hn
      have : 0 < quadraticValue (Q.submatrix Fin.castSucc Fin.castSucc)
          (fun i => y i.castSucc) := by simpa [quadraticValue_eq_dotProduct] using hpos
      linarith
    have hyzero : y = 0 := by
      funext i
      refine Fin.lastCases hylast (fun j => ?_) i
      exact congrFun hycast j
    exact ⟨c, sub_eq_zero.mp hyzero⟩
  · rintro ⟨c, rfl⟩
    rw [quadraticValue_eq_dotProduct, Matrix.mulVec_smul, hv, smul_zero, dotProduct_zero]

/-- Rational principal Gram data lift to PSD of the full real matrix along a checked rational kernel. -/
theorem rational_principal_gram_posSemidef {n r : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hsym : ∀ i j, Q i j = Q j i) (v : Fin (n + 1) → ℚ)
    (hkernel : ∀ i, (∑ j, Q i j * v j) = 0) (hvlast : v (Fin.last n) ≠ 0)
    (C : GramCertificate n r) (hC : C.Valid (Q.submatrix Fin.castSucc Fin.castSucc)) :
    (Q.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply posSemidef_of_principal_kernel (Q.map (fun q : ℚ => (q : ℝ)))
    (v := fun i => (v i : ℝ))
  · ext i j
    change (Q j i : ℝ) = (Q i j : ℝ)
    exact congrArg (fun q : ℚ => (q : ℝ)) (hsym j i)
  · ext i
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hkernel i)
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum,
      Rat.cast_mul, Rat.cast_zero, Pi.zero_apply] using h
  · exact_mod_cast hvlast
  · exact C.posSemidef (Q.submatrix Fin.castSucc Fin.castSucc) hC

/-- Rational centering projection, in the entry convention used by the shifted Gram matrices. -/
def centeringMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => (if i = j then 1 else 0) - (n : ℚ)⁻¹)

/-- The centering projection has the expected variance quadratic form, also for n=0. -/
theorem quadraticValue_centeringMatrix (n : ℕ) (x : Fin n → ℝ) :
    quadraticValue ((centeringMatrix n).map (fun q : ℚ => (q : ℝ))) x =
      (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / n := by
  classical
  unfold quadraticValue centeringMatrix
  simp only [Matrix.map_apply, Matrix.of_apply, Rat.cast_sub, apply_ite, Rat.cast_one, Rat.cast_zero,
    Rat.cast_inv, Rat.cast_natCast, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hdiag : (∑ i, ∑ j, x i * (if i = j then (1 : ℝ) else 0) * x j) = ∑ i, x i ^ 2 := by
    simp [mul_ite, ite_mul, pow_two]
  simp only [← mul_ite]
  rw [hdiag]
  congr 1
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- A PSD rational shift provides the quantitative real lower bound used by stability certificates. -/
theorem quadraticValue_lower_of_centered_shift {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (hshift : ((Q - c • centeringMatrix n).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (x : Fin n → ℝ) :
    (c : ℝ) * ((∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / n) ≤
      quadraticValue (Q.map (fun q : ℚ => (q : ℝ))) x := by
  have hnonneg : 0 ≤ quadraticValue ((Q - c • centeringMatrix n).map (fun q : ℚ => (q : ℝ))) x := by
    simpa [quadraticValue_eq_dotProduct] using hshift.dotProduct_mulVec_nonneg x
  have heq : quadraticValue ((Q - c • centeringMatrix n).map (fun q : ℚ => (q : ℝ))) x =
      quadraticValue (Q.map (fun q : ℚ => (q : ℝ))) x -
        (c : ℝ) * quadraticValue ((centeringMatrix n).map (fun q : ℚ => (q : ℝ))) x := by
    simp only [quadraticValue, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Rat.cast_sub, Rat.cast_mul, mul_sub, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, quadraticValue_centeringMatrix] at hnonneg
  linarith

end DittertRybin.Certificates
