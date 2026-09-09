import DR.Rectangular.OrderThreeFourRowConcentration
import DR.Rectangular.ThreeRowComparison
import DR.Certificates.Gram

/-! A signed-vector quadratic floor for the actual three-sample averaging kernel.
The row neighborhood and deleted mass are independent quantitative hypotheses. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

noncomputable def orderThreeFourRowPairKernel (r : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i=j then ∑ k,r k else r i+r j

theorem orderThreeFourRowPairKernel_sub (r t : Fin 4 → ℝ) :
    orderThreeFourRowPairKernel (fun i => r i-t i) =
      orderThreeFourRowPairKernel r-orderThreeFourRowPairKernel t := by
  ext i j
  by_cases hij : i=j
  · simp [orderThreeFourRowPairKernel,hij,Finset.sum_sub_distrib]
  · simp only [orderThreeFourRowPairKernel,if_neg hij,Matrix.sub_apply]
    ring

theorem orderThreeFourRowPairKernel_frobenius (r : Fin 4 → ℝ) (hr : ∑ i,r i=1) :
    (∑ i,∑ j,(orderThreeFourRowPairKernel r i j-
      orderThreeFourRowPairKernel (fun _ => 1/4) i j)^2)=4*orderThreeFourRowVariance r := by
  have hr3 : r 3=1-r 0-r 1-r 2 := by
    simp only [Fin.sum_univ_four] at hr
    linarith only [hr]
  simp only [orderThreeFourRowPairKernel,orderThreeFourRowVariance,Fin.sum_univ_four]
  norm_num [Fin.ext_iff]
  rw [hr3]
  ring

theorem orderThreeFourRowPairKernel_near_lower (r x : Fin 4 → ℝ)
    (hr : ∑ i,r i=1) (hnear : orderThreeFourRowVariance r≤1/64) :
    (1/4:ℝ)*(∑ i,x i^2)≤quadraticValue (orderThreeFourRowPairKernel r) x := by
  let D := orderThreeFourRowPairKernel r-orderThreeFourRowPairKernel (fun _ => 1/4)
  let E := ∑ i,x i^2
  have hE0 : 0≤E := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun q : Fin 4 × Fin 4 => D q.1 q.2) (fun q => x q.1*x q.2)
  have hleft : (∑ q : Fin 4 × Fin 4,D q.1 q.2*(x q.1*x q.2))=quadraticValue D x := by
    simp only [Fintype.sum_prod_type,quadraticValue]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hright : (∑ q : Fin 4 × Fin 4,(x q.1*x q.2)^2)=E^2 := by
    simp only [Fintype.sum_prod_type,mul_pow,← Finset.mul_sum,← Finset.sum_mul]
    exact (pow_two E).symm
  rw [hleft,hright] at hCS
  have hD : (∑ q : Fin 4 × Fin 4,D q.1 q.2^2)=4*orderThreeFourRowVariance r := by
    simpa only [Fintype.sum_prod_type,D,Matrix.sub_apply] using orderThreeFourRowPairKernel_frobenius r hr
  rw [hD] at hCS
  have hbound := mul_le_mul_of_nonneg_right hnear (sq_nonneg E)
  have hlow : -(E/4)≤quadraticValue D x := by
    nlinarith only [hCS,hbound,hE0]
  have hquad : quadraticValue (orderThreeFourRowPairKernel r) x =
      quadraticValue D x+E/2+(∑ i,x i)^2/2 := by
    dsimp [D,E,quadraticValue,orderThreeFourRowPairKernel]
    simp only [Fin.sum_univ_four]
    norm_num [Fin.ext_iff]
    ring
  rw [hquad]
  nlinarith only [hlow,sq_nonneg (∑ i,x i)]

/-- A deleted nonnegative marginal costs at most four times its total mass. -/
theorem orderThreeFourRowPairKernel_nonneg_upper (t x : Fin 4 → ℝ) (ht : ∀ i,0≤t i) :
    quadraticValue (orderThreeFourRowPairKernel t) x≤4*(∑ i,t i)*(∑ i,x i^2) := by
  have hterm (i j : Fin 4) :
      x i*orderThreeFourRowPairKernel t i j*x j≤
        orderThreeFourRowPairKernel t i j*(x i^2+x j^2)/2 := by
    have hC : 0≤orderThreeFourRowPairKernel t i j := by
      unfold orderThreeFourRowPairKernel
      split_ifs
      · exact Finset.sum_nonneg fun k _ => ht k
      · exact add_nonneg (ht i) (ht j)
    nlinarith only [mul_nonneg hC (sq_nonneg (x i-x j))]
  have hsum := Finset.sum_le_sum fun i (_ : i∈Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j∈Finset.univ) => hterm i j
  change quadraticValue (orderThreeFourRowPairKernel t) x≤_ at hsum
  have hrow : (∑ i,∑ j,orderThreeFourRowPairKernel t i j*(x i^2+x j^2)/2)=
      ∑ i,(2*(∑ j,t j)+2*t i)*x i^2 := by
    simp only [orderThreeFourRowPairKernel,Fin.sum_univ_four]
    norm_num [Fin.ext_iff]
    ring
  rw [hrow] at hsum
  apply hsum.trans
  calc
    _ ≤ ∑ i,4*(∑ j,t j)*x i^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi : t i≤∑ j,t j := Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)
      nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (sq_nonneg (x i))]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem orderThreeFourRowPairKernel_deleted_lower (r t x : Fin 4 → ℝ)
    (hr : ∑ i,r i=1) (hnear : orderThreeFourRowVariance r≤1/64) (ht : ∀ i,0≤t i) :
    (1/4-4*(∑ i,t i))*(∑ i,x i^2)≤
      quadraticValue (orderThreeFourRowPairKernel (fun i => r i-t i)) x := by
  have hlo := orderThreeFourRowPairKernel_near_lower r x hr hnear
  have hup := orderThreeFourRowPairKernel_nonneg_upper t x ht
  rw [orderThreeFourRowPairKernel_sub]
  simp only [quadraticValue,Matrix.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib] at *
  nlinarith only [hlo,hup]

end DittertRybin
