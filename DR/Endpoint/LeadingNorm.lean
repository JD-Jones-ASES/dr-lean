import DR.Endpoint.LeadingUniform
import Mathlib.Algebra.QuadraticDiscriminant

/-! Finite quadratic Cauchy--Schwarz and the leading-gauge norm comparison.
Positive semidefiniteness is an explicit hypothesis. Singular forms and signed
vectors are retained; the leading kernel is not asserted positive everywhere. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

noncomputable def endpointBilinear {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ := ∑ i, ∑ j,x i*Q i j*y j

theorem endpointBilinear_symm {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm) (x y : ι → ℝ) :
    endpointBilinear Q x y=endpointBilinear Q y x := by
  unfold endpointBilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : Q j i=Q i j := congrFun (congrFun hQ.eq i) j
  rw [he]
  ring

theorem endpoint_quadratic_line {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm) (x y : ι → ℝ) (t : ℝ) :
    quadraticValue Q (fun i => t*x i+y i)=
      quadraticValue Q x*t^2+2*endpointBilinear Q x y*t+quadraticValue Q y := by
  have he : quadraticValue Q (fun i => t*x i+y i)=
      t^2*quadraticValue Q x+t*endpointBilinear Q x y+
      t*endpointBilinear Q y x+quadraticValue Q y := by
    unfold quadraticValue endpointBilinear
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,endpointBilinear_symm Q hQ y x]
  ring

theorem endpoint_quadratic_nonneg {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) (x : ι → ℝ) :
    0≤quadraticValue Q x := by
  simpa only [quadraticValue_eq_dotProduct,star_trivial] using hQ.dotProduct_mulVec_nonneg x

theorem endpointBilinear_le_sqrt {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) (x y : ι → ℝ) :
    endpointBilinear Q x y≤Real.sqrt (quadraticValue Q x)*Real.sqrt (quadraticValue Q y) := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hQ.1
  have hdisc := discrim_le_zero (a:=quadraticValue Q x)
    (b:=2*endpointBilinear Q x y) (c:=quadraticValue Q y) (fun t => by
      have h := endpoint_quadratic_nonneg Q hQ (fun i => t*x i+y i)
      rw [endpoint_quadratic_line Q hs x y t] at h
      simpa only [pow_two] using h)
  have hx := Real.sq_sqrt (endpoint_quadratic_nonneg Q hQ x)
  have hy := Real.sq_sqrt (endpoint_quadratic_nonneg Q hQ y)
  have hr : 0≤Real.sqrt (quadraticValue Q x)*Real.sqrt (quadraticValue Q y) := by positivity
  have hsq : (endpointBilinear Q x y)^2≤
      (Real.sqrt (quadraticValue Q x)*Real.sqrt (quadraticValue Q y))^2 := by
    rw [mul_pow,hx,hy]
    unfold discrim at hdisc
    nlinarith only [hdisc]
  nlinarith only [hsq,hr,sq_nonneg (endpointBilinear Q x y-
    Real.sqrt (quadraticValue Q x)*Real.sqrt (quadraticValue Q y))]

theorem endpoint_quadratic_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι ι ℝ) (v : κ → ι → ℝ) :
    quadraticValue Q (fun i => ∑ a,v a i)=∑ a,∑ b,endpointBilinear Q (v a) (v b) := by
  unfold quadraticValue endpointBilinear
  simp only [Finset.sum_mul,Finset.mul_sum]
  calc
    (∑ i : ι,∑ j : ι,∑ b : κ,∑ a : κ,v a i*Q i j*v b j)=
        ∑ i : ι,∑ j : ι,∑ a : κ,∑ b : κ,v a i*Q i j*v b j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _=∑ i : ι,∑ a : κ,∑ j : ι,∑ b : κ,v a i*Q i j*v b j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _=∑ a : κ,∑ i : ι,∑ j : ι,∑ b : κ,v a i*Q i j*v b j := Finset.sum_comm
    _=∑ a : κ,∑ i : ι,∑ b : κ,∑ j : ι,v a i*Q i j*v b j := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _=_ := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm

/-- The finite triangle inequality for any positive semidefinite quadratic form. -/
theorem endpoint_quadratic_sqrt_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) (v : κ → ι → ℝ) :
    Real.sqrt (quadraticValue Q (fun i => ∑ a,v a i))≤
      ∑ a,Real.sqrt (quadraticValue Q (v a)) := by
  have h := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) =>
    Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => endpointBilinear_le_sqrt Q hQ (v a) (v b)))
  rw [← endpoint_quadratic_sum Q v] at h
  have he : (∑ a,∑ b,Real.sqrt (quadraticValue Q (v a))*Real.sqrt (quadraticValue Q (v b)))=
      (∑ a,Real.sqrt (quadraticValue Q (v a)))^2 := by
    rw [pow_two,Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [he] at h
  exact (Real.sqrt_le_iff).mpr ⟨Finset.sum_nonneg (fun a _ => Real.sqrt_nonneg _),h⟩

/-- Actual column costs dominate the marginal norm whenever their common kernel is PSD. -/
theorem endpointLeadingGauge_marginal_lower {m n : ℕ} (P : Board m n)
    (hQ : (endpointLeadingKernel (rowSum P)).PosSemidef) :
    Real.sqrt (quadraticValue (endpointLeadingKernel (rowSum P)) (rowSum P))≤
      endpointLeadingGauge P := by
  exact endpoint_quadratic_sqrt_sum_le _ hQ (fun j i => P i j)

theorem endpointLeadingGauge_product_lower {m n : ℕ} (hm : 2≤m) (P : Board m n)
    (hP : IsProbability P) (hQ : (endpointLeadingKernel (rowSum P)).PosSemidef) :
    Real.sqrt (1-(m.factorial:ℝ)*∏ i,rowSum P i)≤endpointLeadingGauge P := by
  have h := endpointLeadingGauge_marginal_lower P hQ
  rw [endpointLeadingKernel_marginal_value hm] at h
  have hs : (∑ i,rowSum P i)=1 := hP.2
  simpa only [hs,one_pow] using h

end DittertRybin
