import DR.Rectangular.FourRowMinorantDefinitions
import DR.Rectangular.FourRowScalarGaugePolynomial

/-!
# The corrected minorant on two-coordinate faces

The source's square-root/Jensen estimate admits an exact square-completion
proof. Clearing its positive denominator gives a quadratic whose residual
is 3a²/4+T(1-T)(a²-8a+4); its sign follows either from the nonnegative
coefficient or from T(1-T)≤1/4. This handles zero complementary rows too.
-/

namespace DittertRybin
open scoped BigOperators

private theorem two_face_comparison_nonneg (a u v T : ℝ)
    (hs : a+u+v=1) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ T*(4*v^2+2*a*v+a^2)+(1-T)*(4*u^2+2*a*u+a^2)-4*a*T*(1-T) := by
  have hv : v = 1-a-u := by linarith
  rw [hv]
  have hid : T*(4*(1-a-u)^2+2*a*(1-a-u)+a^2)+
      (1-T)*(4*u^2+2*a*u+a^2)-4*a*T*(1-T) =
      (2*u+a*T+a/2-2*T)^2+3*a^2/4+T*(1-T)*(a^2-8*a+4) := by ring
  rw [hid]
  have hw : 0 ≤ T*(1-T) := mul_nonneg hT (by linarith)
  by_cases hc : 0 ≤ a^2-8*a+4
  · exact add_nonneg (add_nonneg (sq_nonneg _) (by positivity)) (mul_nonneg hw hc)
  · have hw1 : T*(1-T) ≤ 1/4 := by nlinarith [sq_nonneg (T-1/2)]
    have hm := mul_le_mul_of_nonpos_right hw1 (le_of_not_ge hc)
    nlinarith [sq_nonneg (2*u+a*T+a/2-2*T),sq_nonneg (a-1)]

noncomputable def fourRowPairCubic (a b x : ℝ) : ℝ :=
  a*x^2+(a^2-2*b)*x+a*b

/-- Exact two-support scalar inequality with its complementary-product constraint. -/
theorem fourRowPairCubic_minorant (a b u v T : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 4*b ≤ a^2)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : a+u+v=1) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ T*fourRowPairCubic a b v+(1-T)*fourRowPairCubic a b u-4*b*T*(1-T) := by
  by_cases ha0 : a=0
  · have hb0 : b=0 := by rw [ha0] at hab; nlinarith
    simp [ha0,hb0,fourRowPairCubic]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hF := two_face_comparison_nonneg a u v T hs hT hT1
  have hD : 0 ≤ a^2-4*b := by linarith
  have hR : 0 ≤ T*((a^2-4*b)*v*(v+a))+(1-T)*((a^2-4*b)*u*(u+a)) := by
    have hT' : 0 ≤ 1-T := by linarith
    positivity
  have hid : a*(T*fourRowPairCubic a b v+(1-T)*fourRowPairCubic a b u-4*b*T*(1-T)) =
      b*(T*(4*v^2+2*a*v+a^2)+(1-T)*(4*u^2+2*a*u+a^2)-4*a*T*(1-T))+
        (T*((a^2-4*b)*v*(v+a))+(1-T)*((a^2-4*b)*u*(u+a))) := by
    unfold fourRowPairCubic
    ring
  have hpos : 0 ≤ a*(T*fourRowPairCubic a b v+(1-T)*fourRowPairCubic a b u-4*b*T*(1-T)) := by
    rw [hid]
    exact add_nonneg (mul_nonneg hb hF) hR
  exact nonneg_of_mul_nonneg_right hpos hap

/-- The actual two-coordinate probability face, including zero rows and T endpoints. -/
theorem fourRowMinorantHomogeneous_two_nonneg {u v y z T : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : u+v+y+z=1) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ fourRowMinorantHomogeneous ![u,v,y,z] ![T,1-T,0,0] := by
  have h := fourRowPairCubic_minorant (y+z) (y*z) u v T (by positivity) (by positivity)
    (by nlinarith [sq_nonneg (y-z)]) hu hv (by linarith) hT hT1
  have hid : fourRowMinorantHomogeneous ![u,v,y,z] ![T,1-T,0,0] =
      T*fourRowPairCubic (y+z) (y*z) v+(1-T)*fourRowPairCubic (y+z) (y*z) u-
        4*(y*z)*T*(1-T) := by
    have hsum : (∑ i, (![u,v,y,z] : Fin 4 → ℝ) i) = 1 := by
      norm_num [Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
      linarith
    simp only [fourRowMinorantHomogeneous,hsum]
    norm_num [fourRowGaugeCollision,fourRowPairCubic,fourRow_complement_product,
      Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,Fin.ext_iff,
      -Fin.val_eq_zero_iff,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rwa [hid]

end DittertRybin
