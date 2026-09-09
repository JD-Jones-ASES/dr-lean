import DR.Square.ProductLoss
import DR.Square.HomogeneousBlocks
import DR.Square.CapacityUnivariate

/-! Product and mass identities for the actual minor blocks in the order-five proof. -/

namespace DittertRybin
open scoped BigOperators

theorem finite_subset_product_le_mean_pow {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (I : Finset (Fin n)) (hI : 0 < I.card) :
    (∏ i ∈ I, r i) ≤ ((∑ i ∈ I, r i) / I.card)^I.card := by
  let e : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
  have h := prod_le_arithMean_pow hI (fun i => r (e i)) (fun i => hr (e i))
  rw [Equiv.prod_comp e (fun i : I => r i), Equiv.sum_comp e (fun i : I => r i)] at h
  simpa only [Finset.prod_coe_sort, Finset.sum_coe_sort] using h

theorem subset_product_lower_of_complement_upper {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (I : Finset (Fin n)) (H : ℝ) (hH : 0 < H)
    (hc : (∏ i ∈ Iᶜ, r i) ≤ H) : (∏ i, r i)/H ≤ ∏ i ∈ I, r i := by
  apply (div_le_iff₀ hH).mpr
  have hp : 0 ≤ ∏ i ∈ I, r i := Finset.prod_nonneg fun i _ => hr i
  have h := mul_le_mul_of_nonneg_left hc hp
  rw [Finset.prod_mul_prod_compl] at h
  exact h

theorem cutMass_transpose_eq {m n : ℕ} (A : Board m n)
    (I : Finset (Fin m)) (J : Finset (Fin n)) :
    cutMass A.transpose J I = cutMass A I J := by
  unfold cutMass
  exact Finset.sum_comm

/-- The full original row products control the actual row sums remaining in a cut block. -/
theorem cut_row_product_loss {m n : ℕ} (A : Board m n) (hA : ∀ i j, 0 ≤ A i j)
    (I : Finset (Fin m)) (J : Finset (Fin n)) (L : ℝ) (hL : 0 < L)
    (hr : ∀ i ∈ I, L ≤ rowSum A i) :
    (∏ i ∈ I, rowSum A i) * (1-cutMass A I Jᶜ/L) ≤
      ∏ i : I, ∑ j ∈ J, A i j := by
  have hsplit (i : Fin m) : rowSum A i = (∑ j ∈ J, A i j)+(∑ j ∈ Jᶜ, A i j) :=
    (Finset.sum_add_sum_compl J (fun j => A i j)).symm
  have hloss := product_loss_lower_common I (rowSum A)
    (fun i => ∑ j ∈ Jᶜ, A i j) L hL hr
    (fun i _ => Finset.sum_nonneg fun j _ => hA i j)
    (by intro i hi; rw [hsplit]; exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => hA i j))
  have heq : (∏ i ∈ I, (rowSum A i-(∑ j ∈ Jᶜ, A i j))) = ∏ i : I, ∑ j ∈ J, A i j := by
    calc
      _ = ∏ i ∈ I, ∑ j ∈ J, A i j := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hsplit]
        ring
      _ = _ := (Finset.prod_coe_sort I (fun i : Fin m => ∑ j ∈ J, A i j)).symm
  rw [heq] at hloss
  exact hloss

/-- The transpose gives the corresponding actual column-product estimate. -/
theorem cut_col_product_loss {m n : ℕ} (A : Board m n) (hA : ∀ i j, 0 ≤ A i j)
    (I : Finset (Fin m)) (J : Finset (Fin n)) (L : ℝ) (hL : 0 < L)
    (hc : ∀ j ∈ J, L ≤ colSum A j) :
    (∏ j ∈ J, colSum A j) * (1-cutMass A Iᶜ J/L) ≤
      ∏ j : J, ∑ i ∈ I, A i j := by
  have h := cut_row_product_loss A.transpose (fun j i => hA i j) J I L hL hc
  rw [cutMass_transpose_eq] at h
  exact h

/-- A bound on the complementary row product gives a bound in terms of the
whole original row product; this is the form used in both actual minor branches. -/
theorem cut_row_product_lower_of_complement_upper {m n : ℕ}
    (A : Board m n) (hA : ∀ i j, 0 ≤ A i j)
    (I : Finset (Fin m)) (J : Finset (Fin n)) (L H : ℝ)
    (hL : 0 < L) (hH : 0 < H) (hr : ∀ i ∈ I, L ≤ rowSum A i)
    (hcomp : (∏ i ∈ Iᶜ, rowSum A i) ≤ H) (hloss : cutMass A I Jᶜ ≤ L) :
    (∏ i, rowSum A i) * ((1-cutMass A I Jᶜ/L)/H) ≤
      ∏ i : I, ∑ j ∈ J, A i j := by
  have hbase := subset_product_lower_of_complement_upper (rowSum A) (rowSum_nonneg hA) I H hH hcomp
  have hfactor : 0 ≤ 1-cutMass A I Jᶜ/L := by
    have h := (div_le_one hL).mpr hloss
    linarith
  calc
    _ = ((∏ i, rowSum A i)/H) * (1-cutMass A I Jᶜ/L) := by ring
    _ ≤ (∏ i ∈ I, rowSum A i) * (1-cutMass A I Jᶜ/L) :=
      mul_le_mul_of_nonneg_right hbase hfactor
    _ ≤ _ := cut_row_product_loss A hA I J L hL hr

theorem cut_col_product_lower_of_complement_upper {m n : ℕ}
    (A : Board m n) (hA : ∀ i j, 0 ≤ A i j)
    (I : Finset (Fin m)) (J : Finset (Fin n)) (L H : ℝ)
    (hL : 0 < L) (hH : 0 < H) (hc : ∀ j ∈ J, L ≤ colSum A j)
    (hcomp : (∏ j ∈ Jᶜ, colSum A j) ≤ H) (hloss : cutMass A Iᶜ J ≤ L) :
    (∏ j, colSum A j) * ((1-cutMass A Iᶜ J/L)/H) ≤
      ∏ j : J, ∑ i ∈ I, A i j := by
  have h := cut_row_product_lower_of_complement_upper A.transpose (fun j i => hA i j)
    J I L H hL hH hc hcomp
    (by rw [cutMass_transpose_eq]; exact hloss)
  rw [cutMass_transpose_eq] at h
  exact h

end DittertRybin
