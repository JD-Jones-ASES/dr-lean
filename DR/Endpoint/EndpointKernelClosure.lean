import DR.Endpoint.ColumnRigidity
import DR.Collision.Averaging
import DR.Certificates.Gram

/-! A positive actual two-column blend kernel forces one-sided endpoint
rigidity. Dimension-range proofs must separately supply the kernel premise
for every actual contender; no probability conclusion is assumed here. -/
namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

theorem endpoint_maximizer_equal_columns_of_kernel {m n : ℕ} (hm : 2≤m)
    (P : Board m n) (hP : IsProbability P)
    (hmax : ∀ Q : Board m n,IsProbability Q→separationProbability Q m≤separationProbability P m)
    (hkernel : ∀ a b : Fin n,a≠b→(averagingKernel (eraseColumns P {a,b}) (m-2)).PosDef) :
    ∀ i a b,P i a=P i b := by
  intro i a b
  by_cases hab : a=b
  · rw [hab]
  let x : Fin m → ℝ := fun j => P j a-P j b
  by_contra hi
  have hx : x≠0 := by
    intro hx
    exact hi (sub_eq_zero.mp (congrFun hx i))
  have hq : 0<quadraticValue (averagingKernel (eraseColumns P {a,b}) (m-2)) x := by
    simpa [quadraticValue_eq_dotProduct] using (hkernel a b hab).dotProduct_mulVec_pos hx
  have hmid := hmax (blendColumns P a b (1/2))
    (blendColumns_isProbability hP a b hab (1/2) (by norm_num) (by norm_num))
  have hid := separationProbability_blend_identity_of_two_le (k:=m) P hm a b hab (1/2)
  have hf : 0<(1/2:ℝ)*(1-1/2)*(m.factorial:ℝ) := by
    have hfac : (0:ℝ)<m.factorial := by exact_mod_cast Nat.factorial_pos m
    positivity
  have hpos := mul_pos hf hq
  change 0<(1/2:ℝ)*(1-1/2)*(m.factorial:ℝ)*
    (∑ j,∑ l,(P j a-P j b)*averagingKernel (eraseColumns P {a,b}) (m-2) j l*(P l a-P l b)) at hpos
  linarith only [hid,hmid,hpos]

theorem uniform_maximum_endpoint_of_contender_kernel {m n : ℕ}
    (hm : 2≤m) (hn : 0<n)
    (hkernel : ∀ P : Board m n,IsProbability P→
      uniformSeparationValue m n m≤separationProbability P m→
      ∀ a b : Fin n,a≠b→(averagingKernel (eraseColumns P {a,b}) (m-2)).PosDef) :
    UniformMaximizer m n m := by
  apply uniform_maximizer_endpoint_of_column_rigidity hm hn
  intro P hP hmax
  have hcont := hmax (uniformBoard m n) (uniformBoard_isProbability (by omega) hn)
  rw [separationProbability_uniform (by omega) hn] at hcont
  exact endpoint_maximizer_equal_columns_of_kernel hm P hP hmax (hkernel P hP hcont)

end DittertRybin
