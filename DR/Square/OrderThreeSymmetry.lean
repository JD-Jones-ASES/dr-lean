import DR.Square.OrderThree

/-! Feasible support-preserving row and column averaging at order three. -/

open scoped BigOperators
open Finset

namespace DittertRybin

theorem totalMass_matrix_transpose {m n : ℕ} (A : Board m n) :
    totalMass A.transpose = totalMass A := by
  unfold totalMass rowSum
  exact Finset.sum_comm

theorem dittert_globalMax_transpose {n : ℕ} {A : Board n n}
    (hmax : ∀ B : Board n n, (∀ i j, 0 ≤ B i j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) :
    ∀ B : Board n n, (∀ i j, 0 ≤ B i j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A.transpose := by
  intro B hB hm
  have h := hmax B.transpose (fun i j => hB j i) ((totalMass_matrix_transpose B).trans hm)
  simpa only [dittertFunctional_transpose] using h

theorem orderThree_same_support_blend_globalMax {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (j k : Fin 3) (hjk : j ≠ k) (hs : ∀ i, 0 < A i j ↔ 0 < A i k)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (∀ i l, 0 ≤ blendThreeColumns A j k t i l) ∧
      totalMass (blendThreeColumns A j k t) = 3 ∧
      ∀ B : Board 3 3, (∀ i l, 0 ≤ B i l) → totalMass B = 3 →
        dittertFunctional B ≤ dittertFunctional (blendThreeColumns A j k t) := by
  obtain ⟨hp, hm⟩ := blendThreeColumns_feasible hA j k hjk ht
  refine ⟨hp, hm.trans hmass, ?_⟩
  rw [dittert_three_same_support_blend_flat hA hmass hmax j k hjk hs]
  exact hmax

theorem orderThree_half_blend_support {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (j k : Fin 3)
    (hs : ∀ i, 0 < A i j ↔ 0 < A i k) (i l : Fin 3) :
    0 < blendThreeColumns A j k (1 / 2) i l ↔ 0 < A i l := by
  have hav (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a ↔ 0 < b) :
      0 < (1-(1/2:ℝ))*a+(1/2:ℝ)*b ↔ 0 < a := by
    constructor
    · intro hp
      by_contra hn
      have ha0 : a = 0 := le_antisymm (le_of_not_gt hn) ha
      have hb0 : b = 0 := le_antisymm (le_of_not_gt (mt hab.mpr hn)) hb
      simp [ha0, hb0] at hp
    · intro hp
      nlinarith
  unfold blendThreeColumns
  split_ifs with hlj hlk
  · subst l
    exact hav _ _ (hA i j) (hA i k) (hs i)
  · subst l
    simpa [add_comm] using hav _ _ (hA i k) (hA i j) (hs i).symm
  · rfl

def blendThreeRows (A : Board 3 3) (i k : Fin 3) (t : ℝ) : Board 3 3 :=
  (blendThreeColumns A.transpose i k t).transpose

theorem orderThree_same_support_row_blend_globalMax {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (i k : Fin 3) (hik : i ≠ k) (hs : ∀ j, 0 < A i j ↔ 0 < A k j)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (∀ r j, 0 ≤ blendThreeRows A i k t r j) ∧
      totalMass (blendThreeRows A i k t) = 3 ∧
      ∀ B : Board 3 3, (∀ r j, 0 ≤ B r j) → totalMass B = 3 →
        dittertFunctional B ≤ dittertFunctional (blendThreeRows A i k t) := by
  obtain ⟨hp, hm, hg⟩ := orderThree_same_support_blend_globalMax (fun i j => hA j i)
    ((totalMass_matrix_transpose A).trans hmass) (dittert_globalMax_transpose hmax) i k hik hs ht
  refine ⟨fun r j => hp j r, ?_, dittert_globalMax_transpose hg⟩
  exact (totalMass_matrix_transpose _).trans hm

theorem orderThree_half_row_blend_support {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (i k : Fin 3)
    (hs : ∀ j, 0 < A i j ↔ 0 < A k j) (r j : Fin 3) :
    0 < blendThreeRows A i k (1 / 2) r j ↔ 0 < A r j :=
  orderThree_half_blend_support (fun i j => hA j i) i k hs j r

end DittertRybin
