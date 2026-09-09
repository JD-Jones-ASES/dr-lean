import DR.Endpoint.RowDeletionClassification
import DR.Certificates.Gram

/-! Pointwise quadratic bounds for the actual two-row deletion matrix.
The deficit-two patterns are the adjacency matrices of K3 and K2,2, and
their exact row sums give the factor two without a spectral assumption. -/

namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

/-- A symmetric matrix with nonnegative entries is bounded in quadratic
form by its diagonal matrix of row sums. No sign condition is imposed on x. -/
theorem quadraticValue_le_rowSums {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0≤Q i j) (hsym : ∀ i j, Q i j=Q j i)
    (x : ι → ℝ) :
    quadraticValue Q x ≤ ∑ i, (∑ j, Q i j)*x i^2 := by
  have hterm (i j : ι) : 2*(x i*Q i j*x j)≤Q i j*(x i^2+x j^2) := by
    have h := mul_nonneg (hQ i j) (sq_nonneg (x i-x j))
    nlinarith
  have h := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hterm i j))
  have he : (∑ i, ∑ j, Q i j*(x i^2+x j^2)) =
      2*∑ i, (∑ j, Q i j)*x i^2 := by
    simp only [mul_add,Finset.sum_add_distrib]
    have hflip : (∑ i, ∑ j, Q i j*x j^2) = ∑ i, (∑ j, Q i j)*x i^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [hsym (j := i)]
      rw [Finset.sum_mul]
    rw [hflip]
    simp only [← Finset.sum_mul]
    ring
  rw [he] at h
  have hl : (∑ i, ∑ j, 2*(x i*Q i j*x j))=2*quadraticValue Q x := by
    simp only [quadraticValue,Finset.mul_sum]
  rw [hl] at h
  linarith

theorem rowDeletionMatrix_nonneg {m n : ℕ} (z : Fin m → Fin n) (i j : Fin m) :
    0≤rowDeletionMatrix z i j := by
  classical
  unfold rowDeletionMatrix
  split_ifs <;> norm_num

theorem sum_rowClassIncidence {m : ℕ} (V : Finset (Fin m)) :
    (∑ i, rowClassIncidence V i)=(V.card : ℝ) := by
  classical
  simp [rowClassIncidence]

theorem RowClassPattern.deletion_rowSum_triple {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=3) (i : Fin m) :
    (∑ j, rowDeletionMatrix z i j)=2*rowClassIncidence V i := by
  classical
  by_cases hi : i∈V
  · have he (j : Fin m) : rowDeletionMatrix z i j=rowClassIncidence (V.erase i) j := by
      rw [hz.deletionMatrix_triple hV]
      by_cases hij : i=j
      · subst j
        simp [rowClassIncidence]
      · simp [rowClassIncidence,hi,hij,Ne.symm hij]
    simp_rw [he]
    rw [sum_rowClassIncidence,Finset.card_erase_of_mem hi,hV]
    norm_num [rowClassIncidence,hi]
  · have he (j : Fin m) : rowDeletionMatrix z i j=0 := by
      rw [hz.deletionMatrix_triple hV]
      simp [hi]
    simp [he,rowClassIncidence,hi]

theorem RowTwoClassPattern.deletion_rowSum_two_pairs {m n : ℕ}
    {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (hV : V.card=2) (hW : W.card=2)
    (hdisj : Disjoint V W) (i : Fin m) :
    (∑ j, rowDeletionMatrix z i j)=2*rowClassIncidence (V∪W) i := by
  classical
  by_cases hiV : i∈V
  · have hiW : i∉W := fun h => Finset.disjoint_left.mp hdisj hiV h
    have he (j : Fin m) : rowDeletionMatrix z i j=rowClassIncidence W j := by
      rw [hz.deletionMatrix_two_pairs hV hW hdisj]
      by_cases hij : i=j
      · subst j
        simp [rowClassIncidence,hiW]
      · simp [rowClassIncidence,hiV,hiW,hij]
    simp_rw [he]
    rw [sum_rowClassIncidence,hW]
    norm_num [rowClassIncidence,hiV]
  · by_cases hiW : i∈W
    · have he (j : Fin m) : rowDeletionMatrix z i j=rowClassIncidence V j := by
        rw [hz.deletionMatrix_two_pairs hV hW hdisj]
        by_cases hij : i=j
        · subst j
          simp [rowClassIncidence,hiV]
        · simp [rowClassIncidence,hiV,hiW,hij]
      simp_rw [he]
      rw [sum_rowClassIncidence,hV]
      norm_num [rowClassIncidence,hiW]
    · have he (j : Fin m) : rowDeletionMatrix z i j=0 := by
        rw [hz.deletionMatrix_two_pairs hV hW hdisj]
        simp [hiV,hiW]
      simp [he,rowClassIncidence,hiV,hiW]

theorem RowClassPattern.neg_deletion_quadratic_triple {m n : ℕ}
    {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=3) (x : Fin m → ℝ) :
    -2*(∑ i, rowClassIncidence V i*x i^2)≤-quadraticValue (rowDeletionMatrix z) x := by
  have h := quadraticValue_le_rowSums (rowDeletionMatrix z) (rowDeletionMatrix_nonneg z)
    (fun i j => (rowDeletionMatrix_symmetric z).apply j i) x
  simp_rw [hz.deletion_rowSum_triple hV] at h
  have he : (∑ i, 2*rowClassIncidence V i*x i^2)=2*∑ i, rowClassIncidence V i*x i^2 := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he] at h
  linarith

theorem RowTwoClassPattern.neg_deletion_quadratic_two_pairs {m n : ℕ}
    {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (hV : V.card=2) (hW : W.card=2)
    (hdisj : Disjoint V W) (x : Fin m → ℝ) :
    -2*(∑ i, rowClassIncidence (V∪W) i*x i^2)≤-quadraticValue (rowDeletionMatrix z) x := by
  have h := quadraticValue_le_rowSums (rowDeletionMatrix z) (rowDeletionMatrix_nonneg z)
    (fun i j => (rowDeletionMatrix_symmetric z).apply j i) x
  simp_rw [hz.deletion_rowSum_two_pairs hV hW hdisj] at h
  have he : (∑ i, 2*rowClassIncidence (V∪W) i*x i^2)=2*∑ i, rowClassIncidence (V∪W) i*x i^2 := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he] at h
  linarith

/-- An injective assignment contributes the exact identity-minus-ones
quadratic form. -/
theorem neg_deletion_quadratic_of_injective {m n : ℕ} {z : Fin m → Fin n}
    (hz : Function.Injective z) (x : Fin m → ℝ) :
    -quadraticValue (rowDeletionMatrix z) x=(∑ i, x i^2)-(∑ i, x i)^2 := by
  classical
  have he (i j : Fin m) : rowDeletionMatrix z i j=1-(if i=j then 1 else 0) := by
    rw [rowDeletionMatrix_of_injective hz]
    split_ifs <;> norm_num
  unfold quadraticValue
  simp_rw [he]
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib,mul_one]
  have hd : (∑ i, ∑ j, x i*(if i=j then (1:ℝ) else 0)*x j)=∑ i,x i^2 := by
    simp [mul_ite,ite_mul,pow_two]
  rw [hd]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  ring

/-- The exact rank-one remainder is a square. Its sign is valid for every
real vector, including vectors with mixed coordinate signs. -/
theorem RowClassPattern.neg_deletion_quadratic_pair {m n : ℕ}
    {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=2) (x : Fin m → ℝ) :
    -quadraticValue (rowDeletionMatrix z) x=
      (∑ i, rowClassIncidence V i*x i^2)-
      2*(∑ i,x i)*(∑ i,rowClassIncidence V i*x i)+
      (∑ i,rowClassIncidence V i*x i)^2 := by
  classical
  have he : -quadraticValue (rowDeletionMatrix z) x=
      ∑ i,∑ j,x i*(-rowDeletionMatrix z i j)*x j := by
    simp [quadraticValue,Finset.sum_neg_distrib]
  rw [he]
  simp_rw [hz.neg_deletionMatrix_pair hV]
  simp only [mul_add,mul_sub,add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hd : (∑ i,∑ j,x i*(if i=j then rowClassIncidence V i else 0)*x j)=
      ∑ i,rowClassIncidence V i*x i^2 := by
    simp only [mul_ite,ite_mul,zero_mul,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hd]
  have hc1 : (∑ i,∑ j,x i*rowClassIncidence V i*x j)=
      (∑ i,rowClassIncidence V i*x i)*(∑ i,x i) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hc2 : (∑ i,∑ j,x i*rowClassIncidence V j*x j)=
      (∑ i,x i)*(∑ i,rowClassIncidence V i*x i) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hr : (∑ i,∑ j,x i*(rowClassIncidence V i*rowClassIncidence V j)*x j)=
      (∑ i,rowClassIncidence V i*x i)^2 := by
    rw [pow_two,Finset.mul_sum]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hc1,hc2,hr]
  ring

theorem RowClassPattern.neg_deletion_quadratic_pair_lower {m n : ℕ}
    {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=2) (x : Fin m → ℝ) :
    (∑ i,rowClassIncidence V i*x i^2)-2*(∑ i,x i)*(∑ i,rowClassIncidence V i*x i)≤
      -quadraticValue (rowDeletionMatrix z) x := by
  rw [hz.neg_deletion_quadratic_pair hV]
  exact le_add_of_nonneg_right (sq_nonneg _)

end DittertRybin
