import DR.Square.OrderFourPolynomialCoefficients

/-!
# A kernel-computable sorted-list coefficient interface

Mathlib's quotient sort is appropriate for the semantic polynomial. For
finite checking, an already sorted list gives the same vector by the proved
mergeSort identity. Erasing either quadratic cell preserves sortedness.
-/

namespace DittertRybin

open scoped BigOperators

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable def orderFourListRawMatrix (l : List (Fin 16)) :
    Matrix (Fin 16) (Fin 16) ℚ :=
  if hl : l.length = 4 then
    orderFourMultiplierMatrix ⟨(l.map Fin.val).toArray, by simpa using hl⟩
  else 0

theorem orderFourRawMatrix_sorted_list (l : List (Fin 16)) (hl : l.Pairwise (· ≤ ·)) :
    orderFourRawMatrix (l : Multiset (Fin 16)) = orderFourListRawMatrix l := by
  classical
  by_cases hlen : l.length = 4
  · have hcard : (l : Multiset (Fin 16)).card = 4 := by simpa using hlen
    rw [orderFourRawMatrix, dif_pos hcard, orderFourListRawMatrix, dif_pos hlen]
    apply congrArg orderFourMultiplierMatrix
    apply Vector.toList_inj.mp
    rw [orderFourSortedMultiplier_toList]
    simp only [Multiset.coe_sort, List.mergeSort_eq_self _ hl]
    rfl
  · have hcard : (l : Multiset (Fin 16)).card ≠ 4 := by simpa using hlen
    rw [orderFourRawMatrix, dif_neg hcard, orderFourListRawMatrix, dif_neg hlen]

noncomputable def orderFourCertificateListCoefficient (l : List (Fin 16)) : ℚ :=
  ∑ i : Fin 16, if i ∈ l then
    ∑ j : Fin 16, if j ∈ l.erase i then orderFourListRawMatrix ((l.erase i).erase j) i j else 0
    else 0

theorem orderFourCertificateCoefficient_sorted_list (l : List (Fin 16))
    (hl : l.Pairwise (· ≤ ·)) :
    orderFourCertificateCoefficient (l : Multiset (Fin 16)) =
      orderFourCertificateListCoefficient l := by
  classical
  unfold orderFourCertificateCoefficient orderFourCertificateListCoefficient
  simp only [Multiset.mem_coe, Multiset.coe_erase]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · apply Finset.sum_congr rfl
    intro j hj
    split_ifs
    · have h1 : (l.erase i).Pairwise (· ≤ ·) := hl.sublist List.erase_sublist
      have h2 : ((l.erase i).erase j).Pairwise (· ≤ ·) := h1.sublist List.erase_sublist
      rw [orderFourRawMatrix_sorted_list _ h2]
    · rfl
  · rfl

end DittertRybin
