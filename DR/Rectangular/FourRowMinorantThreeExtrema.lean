import DR.Rectangular.FourRowMinorantThreeCurve
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact fixed-moment reduction to boundaries or repeated rows

Every affine function of the three-coordinate product attains its minimum
on the actual closed feasibility set. It has a minimizing point where a
coordinate vanishes, a coordinate feasibility constraint is active, or two
coordinates coincide. The zero product coefficient is handled by choosing
a product minimum, so no nonzero-coefficient assumption is hidden.
-/

namespace DittertRybin
open scoped BigOperators

theorem threeMomentFeasible_isClosed (s t : ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    IsClosed (threeMomentFeasible s t φ) := by
  have hrow : IsClosed {r : Fin 3 → ℝ | ∀ i, 0 ≤ r i} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter (fun i : Fin 3 => isClosed_le (g := fun r : Fin 3 → ℝ => r i)
        (f := fun _ => 0) continuous_const (continuous_apply i))
  have hsum : IsClosed {r : Fin 3 → ℝ | (∑ i, r i)=s} :=
    isClosed_eq (by fun_prop) continuous_const
  have hpair : IsClosed {r : Fin 3 → ℝ | r 0*r 1+r 0*r 2+r 1*r 2=t} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcon : IsClosed {r : Fin 3 → ℝ | ∀ i, 0 ≤ φ (r i)} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter (fun i : Fin 3 => isClosed_le (g := fun r : Fin 3 → ℝ => φ (r i))
        (f := fun _ => 0) continuous_const (hφ.comp (continuous_apply i)))
  exact hrow.inter (hsum.inter (hpair.inter hcon))

theorem threeMomentFeasible_isCompact (s t : ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    IsCompact (threeMomentFeasible s t φ) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := fun _ : Fin 3 => (0 : ℝ)) (b := fun _ => s))
    (threeMomentFeasible_isClosed s t φ hφ)
  intro r hr
  refine ⟨hr.1,fun i => ?_⟩
  calc
    r i ≤ ∑ j, r j := Finset.single_le_sum (fun j _ => hr.1 j) (Finset.mem_univ i)
    _ = s := hr.2.1

/-- A concrete minimizing point for every affine-product objective, with the
complete boundary/repeated-coordinate alternative. The conclusion applies
when the affine coefficient is zero as well as either strict sign. -/
theorem threeMomentFeasible_exists_affine_minimum (s t A B : ℝ) (φ : ℝ → ℝ)
    (hφ : Continuous φ) (hne : (threeMomentFeasible s t φ).Nonempty) :
    ∃ r ∈ threeMomentFeasible s t φ,
      (∀ u ∈ threeMomentFeasible s t φ, A+B*(∏ i, r i) ≤ A+B*(∏ i, u i)) ∧
      ((∃ i, r i = 0) ∨ (∃ i, φ (r i) = 0) ∨
        r 0 = r 1 ∨ r 0 = r 2 ∨ r 1 = r 2) := by
  classical
  have hc := threeMomentFeasible_isCompact s t φ hφ
  have hp : Continuous (fun r : Fin 3 → ℝ => ∏ i, r i) := by fun_prop
  have hex : ∃ r ∈ threeMomentFeasible s t φ,
      IsExtrOn (fun u => ∏ i, u i) (threeMomentFeasible s t φ) r ∧
      ∀ u ∈ threeMomentFeasible s t φ, A+B*(∏ i, r i) ≤ A+B*(∏ i, u i) := by
    by_cases hB : 0 ≤ B
    · obtain ⟨r,hr,hmin⟩ := hc.exists_isMinOn hne hp.continuousOn
      exact ⟨r,hr,hmin.isExtr,fun u hu => add_le_add_right
        (mul_le_mul_of_nonneg_left (hmin hu) hB) A⟩
    · obtain ⟨r,hr,hmax⟩ := hc.exists_isMaxOn hne hp.continuousOn
      exact ⟨r,hr,hmax.isExtr,fun u hu => add_le_add_right
        (mul_le_mul_of_nonpos_left (hmax hu) (le_of_not_ge hB)) A⟩
  obtain ⟨r,hr,hext,hmin⟩ := hex
  refine ⟨r,hr,hmin,?_⟩
  by_cases hz : ∃ i, r i=0
  · exact Or.inl hz
  right
  by_cases hc0 : ∃ i, φ (r i)=0
  · exact Or.inl hc0
  right
  have hrp : ∀ i, 0 < r i := fun i =>
    lt_of_le_of_ne (hr.1 i) (Ne.symm (fun h => hz ⟨i,h⟩))
  have hcp : ∀ i, 0 < φ (r i) := fun i =>
    lt_of_le_of_ne (hr.2.2.2 i) (Ne.symm (fun h => hc0 ⟨i,h⟩))
  exact threeMomentFeasible_product_extremum_repeated s t φ hφ r hrp hr.2.1
    hr.2.2.1 hcp hext

end DittertRybin
