import DR.Square.OrderFourPolynomialCoefficients
import Mathlib.Data.Fintype.Perm

/-!
# Finite word extraction for the actual quartic

Distributing each row or column product gives 256 words. The permanent is
the sum over the 24 bijective words. The coefficient formula below compares
multisets of physical cells, avoiding noncomputable polynomial normalization.
-/

namespace DittertRybin

open MvPolynomial
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem orderFour_prod_X_list (l : List (Fin 16)) :
    (l.map (X (R := ℚ))).prod = monomial (Multiset.toFinsupp (l : Multiset (Fin 16))) 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    change X a * monomial _ 1 = monomial (Multiset.toFinsupp (a ::ₘ (l : Multiset (Fin 16)))) 1
    rw [orderFour_toFinsupp_cons]
    change monomial (Finsupp.single a 1) (1:ℚ) * monomial _ 1 = _
    rw [monomial_mul, one_mul]

def orderFourRowWord (f : Fin 4 → Fin 4) : Multiset (Fin 16) :=
  (List.ofFn (fun i => orderFourCell (i,f i)) : List (Fin 16))

def orderFourColWord (f : Fin 4 → Fin 4) : Multiset (Fin 16) :=
  (List.ofFn (fun i => orderFourCell (f i,i)) : List (Fin 16))

theorem orderFour_row_product_word (f : Fin 4 → Fin 4) :
    (∏ i : Fin 4, (X (orderFourCell (i,f i)) : MvPolynomial (Fin 16) ℚ)) =
      monomial (orderFourRowWord f).toFinsupp 1 := by
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_apply, orderFourRowWord] using
    orderFour_prod_X_list (List.ofFn (fun i => orderFourCell (i,f i)))

theorem orderFour_col_product_word (f : Fin 4 → Fin 4) :
    (∏ i : Fin 4, (X (orderFourCell (f i,i)) : MvPolynomial (Fin 16) ℚ)) =
      monomial (orderFourColWord f).toFinsupp 1 := by
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_apply, orderFourColWord] using
    orderFour_prod_X_list (List.ofFn (fun i => orderFourCell (f i,i)))

theorem orderFourLabelPermutation_injective : Function.Injective orderFourLabelPermutation := by
  have h : ∀ r t : Fin 24, orderFourLabelPermutationMap r = orderFourLabelPermutationMap t → r = t := by
    decide +kernel
  intro r t hrt
  exact h r t (congrArg (fun e : Equiv.Perm (Fin 4) => (e : Fin 4 → Fin 4)) hrt)

theorem orderFourLabelPermutation_bijective : Function.Bijective orderFourLabelPermutation := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨orderFourLabelPermutation_injective, ?_⟩
  simp [Fintype.card_perm, Nat.factorial]

noncomputable def orderFourQuarticCoefficientCompute (s : Multiset (Fin 16)) : ℚ :=
  24 * ((∑ f : Fin 4 → Fin 4, if orderFourRowWord f = s then 1 else 0) +
    (∑ f : Fin 4 → Fin 4, if orderFourColWord f = s then 1 else 0) -
    ∑ r : Fin 24, if orderFourColWord (orderFourLabelPermutationMap r) = s then 1 else 0)

theorem orderFourQuarticPolynomial_coeff_compute (s : Multiset (Fin 16)) :
    coeff s.toFinsupp orderFourQuarticPolynomial = orderFourQuarticCoefficientCompute s := by
  classical
  have hrow : (∏ i : Fin 4, ∑ j : Fin 4,
      (X (orderFourCell (i,j)) : MvPolynomial (Fin 16) ℚ)) =
      ∑ f : Fin 4 → Fin 4, monomial (orderFourRowWord f).toFinsupp 1 := by
    rw [Fintype.prod_sum]
    exact Finset.sum_congr rfl (fun f hf => orderFour_row_product_word f)
  have hcol : (∏ j : Fin 4, ∑ i : Fin 4,
      (X (orderFourCell (i,j)) : MvPolynomial (Fin 16) ℚ)) =
      ∑ f : Fin 4 → Fin 4, monomial (orderFourColWord f).toFinsupp 1 := by
    rw [Fintype.prod_sum]
    exact Finset.sum_congr rfl (fun f hf => orderFour_col_product_word f)
  have hperm : Matrix.permanent (fun i j : Fin 4 =>
      (X (orderFourCell (i,j)) : MvPolynomial (Fin 16) ℚ)) =
      ∑ r : Fin 24, monomial (orderFourColWord (orderFourLabelPermutationMap r)).toFinsupp 1 := by
    unfold Matrix.permanent
    rw [← Equiv.sum_comp (Equiv.ofBijective orderFourLabelPermutation orderFourLabelPermutation_bijective)]
    exact Finset.sum_congr rfl (fun r hr => orderFour_col_product_word (orderFourLabelPermutationMap r))
  rw [orderFourQuarticPolynomial, hrow, hcol, hperm]
  simp only [coeff_C_mul, coeff_sub, coeff_add, coeff_sum, coeff_monomial,
    Multiset.toFinsupp.injective.eq_iff, orderFourQuarticCoefficientCompute]

end DittertRybin
