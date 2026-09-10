import DR.Definitions
import DR.Certificates.Gram
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

/-!
# The general endpoint leading kernel

The polynomial complementary-product definition retains every boundary row.
The rank-one criterion follows from finite Cauchy--Schwarz, generalizing the
four-row criterion. The column cost is the square root of the kernel
quadratic form; summing it defines the leading gauge. No minimum or
positivity assumption is built into the kernel definition.
-/
namespace DittertRybin
open scoped BigOperators
open Certificates

noncomputable def endpointLeadingKernel {m : ℕ} (r : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i=j then 1 else
    1-((m-2).factorial:ℝ)*∏ a ∈ (Finset.univ.erase i).erase j,r a

noncomputable def endpointLeadingScale {m : ℕ} (r : Fin m → ℝ) : ℝ :=
  ((m-2).factorial:ℝ)*∏ i,r i

noncomputable def endpointLeadingColumnCost {m n : ℕ} (P : Board m n) (j : Fin n) : ℝ :=
  Real.sqrt (quadraticValue (endpointLeadingKernel (rowSum P)) (fun i => P i j))

noncomputable def endpointLeadingGauge {m n : ℕ} (P : Board m n) : ℝ :=
  ∑ j,endpointLeadingColumnCost P j

theorem endpointLeadingKernel_symmetric {m : ℕ} (r : Fin m → ℝ) (i j : Fin m) :
    endpointLeadingKernel r i j=endpointLeadingKernel r j i := by
  simp only [endpointLeadingKernel,eq_comm,Finset.erase_right_comm]

/-- Exact polynomial conjugacy, including zero and signed row coordinates. -/
theorem endpointLeadingKernel_conjugacy {m : ℕ} (r : Fin m → ℝ) (i j : Fin m) :
    r i*r j*endpointLeadingKernel r i j=
      (if i=j then endpointLeadingScale r else 0)+r i*r j-endpointLeadingScale r := by
  classical
  by_cases hij : i=j
  · subst j
    simp [endpointLeadingKernel]
  · have h1 := Finset.prod_erase_mul (Finset.univ.erase i) r
      (show j∈Finset.univ.erase i by simp [Ne.symm hij])
    have h2 := Finset.prod_erase_mul Finset.univ r (Finset.mem_univ i)
    have hp : (∏ a ∈ (Finset.univ.erase i).erase j,r a)*r j*r i=∏ a,r a := by
      rw [h1,h2]
    simp only [endpointLeadingKernel,if_neg hij,zero_add,endpointLeadingScale]
    nlinarith only [congrArg (fun a : ℝ => ((m-2).factorial:ℝ)*a) hp]

/-- The actual quadratic form after row scaling; no row is divided out. -/
theorem endpointLeadingKernel_scaled_quadratic {m : ℕ} (r x : Fin m → ℝ) :
    quadraticValue (endpointLeadingKernel r) (fun i => r i*x i)=
      endpointLeadingScale r*(∑ i,x i^2)+(∑ i,r i*x i)^2-
      endpointLeadingScale r*(∑ i,x i)^2 := by
  classical
  have he (i j : Fin m) : (r i*x i)*endpointLeadingKernel r i j*(r j*x j)=
      x i*(if i=j then endpointLeadingScale r else 0)*x j+
      (r i*x i)*(r j*x j)-endpointLeadingScale r*(x i*x j) := by
    have h := congrArg (fun a : ℝ => x i*a*x j) (endpointLeadingKernel_conjugacy r i j)
    nlinarith only [h]
  unfold quadraticValue
  simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hd : (∑ i,∑ j,x i*(if i=j then endpointLeadingScale r else 0)*x j)=
      endpointLeadingScale r*∑ i,x i^2 := by
    simp only [mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq,
      Finset.mem_univ,if_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hd]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  ring

/-- Cauchy--Schwarz in the diagonal-plus-one quadratic form, without matrix inverses. -/
theorem endpoint_rank_one_cauchy {m : ℕ} (s y : Fin m → ℝ) (hsum : ∑ i, s i = 1)
    (p : ℝ) (hp : 0 < p) :
    p * (∑ i, y i) ^ 2 ≤
      ((m:ℝ) - 1 / ((∑ i, s i ^ 2) + p)) *
        (p * (∑ i, y i ^ 2) + (∑ i, s i * y i) ^ 2) := by
  let q := ∑ i, s i ^ 2
  let d := q + p
  let z := ∑ i, s i * y i
  let v := fun i => 1 - s i / d
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hd : 0 < d := add_pos_of_nonneg_of_pos hq hp
  have hd0 := ne_of_gt hd
  let f : Option (Fin m) → ℝ := fun i => i.elim (z ^ 2) (fun j => p * y j ^ 2)
  let g : Option (Fin m) → ℝ := fun i => i.elim ((p / d) ^ 2) (fun j => p * v j ^ 2)
  let r : Option (Fin m) → ℝ := fun i => i.elim (z * (p / d)) (fun j => p * y j * v j)
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := r) (f := f) (g := g)
    (fun i _ => by cases i <;> dsimp [f] <;> positivity)
    (fun i _ => by cases i <;> dsimp [g] <;> positivity)
    (fun i _ => by cases i <;> dsimp [r, f, g] <;> nlinarith)
  have hv : ∑ i, v i ^ 2 = (m:ℝ) - 2 / d + q / d ^ 2 := by
    simp only [v, sub_sq, one_pow, div_pow, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum, hsum]
    dsimp [q]
    ring
  have hr : ∑ i, r i = p * ∑ i, y i := by
    have hy : (∑ i, p * y i * (s i / d)) = p * z / d := by
      calc
        _ = ∑ i, (p / d) * (s i * y i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (p / d) * z := by rw [← Finset.mul_sum]
        _ = _ := by ring
    simp only [Fintype.sum_option, r, Option.elim, v, mul_sub, mul_one,
      Finset.sum_sub_distrib, hy, ← Finset.mul_sum]
    ring
  have hf : ∑ i, f i = p * (∑ i, y i ^ 2) + z ^ 2 := by
    simp [Fintype.sum_option, f, ← Finset.mul_sum, add_comm]
  have hg : ∑ i, g i = p * ((m:ℝ) - 1 / d) := by
    simp only [Fintype.sum_option, g, Option.elim, ← Finset.mul_sum, hv]
    dsimp [d]
    field_simp
    ring
  rw [hr, hf, hg] at h
  have hdiv := (mul_le_mul_iff_right₀ hp).mp (show
      p * (p * (∑ i, y i) ^ 2) ≤ p * (((m:ℝ) - 1 / d) * (p * (∑ i, y i ^ 2) + z ^ 2)) by
    nlinarith [h])
  exact hdiv


/-- The diagonal-plus-one form gives the full leading-kernel criterion. -/
theorem endpointLeadingKernel_scaled_rank_one_lower {m : ℕ} (r x : Fin m → ℝ)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1) :
    (1/((∑ i,r i^2)+endpointLeadingScale r)-((m:ℝ)-1))*
      (endpointLeadingScale r*(∑ i,x i^2)+(∑ i,r i*x i)^2) ≤
      quadraticValue (endpointLeadingKernel r) (fun i => r i*x i) := by
  have hp : 0<endpointLeadingScale r := mul_pos
    (by exact_mod_cast Nat.factorial_pos (m-2)) (Finset.prod_pos (fun i _ => hr i))
  have h := endpoint_rank_one_cauchy r x hs (endpointLeadingScale r) hp
  rw [endpointLeadingKernel_scaled_quadratic]
  nlinarith only [h]

/-- Strict definiteness is derived from the scalar marginal criterion.
The kernel remains its original complementary-product polynomial. -/
theorem endpointLeadingKernel_posDef {m : ℕ} (r : Fin m → ℝ)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hc : ((m:ℝ)-1)*((∑ i,r i^2)+endpointLeadingScale r)<1) :
    (endpointLeadingKernel r).PosDef := by
  have hp : 0<endpointLeadingScale r := mul_pos
    (by exact_mod_cast Nat.factorial_pos (m-2)) (Finset.prod_pos (fun i _ => hr i))
  have hd : 0<(∑ i,r i^2)+endpointLeadingScale r := add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg (fun i _ => sq_nonneg (r i))) hp
  have hcoef : 0<1/((∑ i,r i^2)+endpointLeadingScale r)-((m:ℝ)-1) := by
    have h := (lt_div_iff₀ hd).mpr hc
    linarith
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    exact fun i j => endpointLeadingKernel_symmetric r j i
  · intro x hx
    let y : Fin m → ℝ := fun i => x i/r i
    have he : (fun i => r i*y i)=x := by
      funext i
      exact mul_div_cancel₀ (x i) (hr i).ne'
    have hy : y≠0 := by
      intro hy
      apply hx
      rw [← he]
      simp only [hy,Pi.zero_apply,mul_zero]
      rfl
    have hy2 : 0<∑ i,y i^2 := by
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hy
      exact (sq_pos_of_ne_zero hi).trans_le
        (Finset.single_le_sum (fun i _ => sq_nonneg (y i)) (Finset.mem_univ i))
    have hbase : 0<endpointLeadingScale r*(∑ i,y i^2)+(∑ i,r i*y i)^2 :=
      add_pos_of_pos_of_nonneg (mul_pos hp hy2) (sq_nonneg _)
    have hbound := endpointLeadingKernel_scaled_rank_one_lower r y hr hs
    have hpos := (mul_pos hcoef hbase).trans_le hbound
    rw [he] at hpos
    simpa [quadraticValue_eq_dotProduct] using hpos

end DittertRybin
