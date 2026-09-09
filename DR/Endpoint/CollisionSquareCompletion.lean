import DR.Endpoint.CollisionSquareCompletionScalar
import DR.Certificates.Gram
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The exact 3/32 gap for the endpoint collision lower matrix.
All assumptions are scalar moment and normalization estimates; positivity
of the desired matrix is proved here. -/
namespace DittertRybin
open Certificates
open scoped BigOperators
noncomputable section

def endpointCollisionLowerMatrix {m : ℕ} (s t v : Fin m → ℝ) (sigma : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (if i=j then 1+t i-2*v i else 0)+sigma*s i*s j-1-t i-t j

theorem endpointCollisionLowerMatrix_quadratic {m : ℕ} (s t v : Fin m → ℝ)
    (sigma : ℝ) (x : Fin m → ℝ) :
    quadraticValue (endpointCollisionLowerMatrix s t v sigma) x =
      (∑ i, (1+t i-2*v i)*(x i)^2)+sigma*(∑ i, s i*x i)^2-
        (∑ i, x i)^2-2*(∑ i, t i*x i)*(∑ i, x i) := by
  classical
  have he (i j : Fin m) : x i*endpointCollisionLowerMatrix s t v sigma i j*x j =
      (if i=j then (1+t i-2*v i)*(x i)^2 else 0)+
        sigma*(s i*x i)*(s j*x j)-x i*x j-(t i*x i)*x j-x i*(t j*x j) := by
    by_cases hij : i=j
    · subst j
      norm_num [endpointCollisionLowerMatrix]
      ring
    · simp only [endpointCollisionLowerMatrix,if_neg hij]
      ring
  unfold quadraticValue
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [←Finset.mul_sum,←Finset.sum_mul]
  ring

/-- Pure matrix criterion used after the actual collision and rook estimates. -/
theorem endpoint_collision_lower_matrix_gap {m : ℕ} (hm : 3 ≤ m)
    (s t v : Fin m → ℝ) (sigma : ℝ)
    (ht : ∀ i, 0 ≤ t i)
    (he : (∑ i, (1-(m:ℝ)*s i)^2) ≤ 1/9)
    (htheta : (∑ i, t i)/(m:ℝ) ≤ 1/4)
    (hell : (∑ i, (t i-(∑ j, t j)/(m:ℝ))^2) ≤ 1/64)
    (hv : ∀ i, v i ≤ 1/4) (hsigma : 4*(m:ℝ)^2 ≤ sigma)
    (x : Fin m → ℝ) :
    (3/32)*(∑ i, (x i)^2) ≤ quadraticValue (endpointCollisionLowerMatrix s t v sigma) x := by
  let theta : ℝ := (∑ i, t i)/(m:ℝ)
  let e : Fin m → ℝ := fun i => 1-(m:ℝ)*s i
  let ell : Fin m → ℝ := fun i => t i-theta
  let N : ℝ := ∑ i, (x i)^2
  let E : ℝ := ∑ i, e i*x i
  let L : ℝ := ∑ i, ell i*x i
  let S : ℝ := ∑ i, s i*x i
  let X : ℝ := ∑ i, x i
  let T : ℝ := ∑ i, t i*x i
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hN : 0 ≤ N := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have htheta0 : 0 ≤ theta :=
    div_nonneg (Finset.sum_nonneg (fun i _ => ht i)) hmpos.le
  have hA0 : 0 ≤ 1+2*theta := by linarith
  have hAupper : 1+2*theta ≤ 3/2 := by dsimp [theta]; linarith
  have hE : E^2 ≤ N/9 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ e x
    have hb := mul_le_mul_of_nonneg_right he hN
    change E^2 ≤ (∑ i, (e i)^2)*N at hc
    change (∑ i, (e i)^2)*N ≤ (1/9)*N at hb
    nlinarith only [hc,hb]
  have hL : L^2 ≤ N/64 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ell x
    have hb := mul_le_mul_of_nonneg_right hell hN
    change L^2 ≤ (∑ i, (ell i)^2)*N at hc
    change (∑ i, (ell i)^2)*N ≤ (1/64)*N at hb
    nlinarith only [hc,hb]
  have hx : (m:ℝ)*S+E=X := by
    dsimp [E,e,S,X]
    simp only [sub_mul,one_mul,mul_assoc,Finset.sum_sub_distrib,←Finset.mul_sum]
    ring
  have hT : T=theta*X+L := by
    dsimp [T,X,L,ell]
    simp only [sub_mul,Finset.sum_sub_distrib,←Finset.mul_sum]
    ring
  have hd : (1/2)*N ≤ ∑ i, (1+t i-2*v i)*(x i)^2 := by
    dsimp only [N]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (by have := ht i; have := hv i; linarith) (sq_nonneg (x i))
  have hscalar := endpoint_scalar_completion_gap (m:ℝ) (1+2*theta) sigma S E L N
    hmpos hA0 hAupper hsigma hE hL
  rw [hx] at hscalar
  rw [endpointCollisionLowerMatrix_quadratic]
  change (3/32)*N ≤ (∑ i, (1+t i-2*v i)*(x i)^2)+sigma*S^2-X^2-2*T*X
  rw [hT]
  nlinarith only [hscalar,hd]

end
end DittertRybin
