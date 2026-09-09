import DR.Square.Transport
import DR.Square.CapacityBound
import DR.Square.Permanent

/-!
# Permanent floors for nearly complete substochastic blocks

A substochastic square matrix of mass `k - x`, with `0 ≤ x < 1`, dominates
`(1 - x)` times a doubly stochastic matrix. Transport cuts and the proved
van der Waerden inequality therefore give the multiplicative power floor.
-/

namespace DittertRybin

open scoped BigOperators
open Matrix

/-- Removing complementary rows and columns loses at most their cardinalities. -/
theorem substochastic_cut_lower {k : ℕ} (Z : Board k k)
    (hZ : ∀ i j, 0 ≤ Z i j) (hr : ∀ i, rowSum Z i ≤ 1)
    (hc : ∀ j, colSum Z j ≤ 1) (x : ℝ) (hmass : totalMass Z = k - x)
    (I J : Finset (Fin k)) :
    (I.card : ℝ) + J.card - k - x ≤ cutMass Z I J := by
  have hrows : (∑ i ∈ I, rowSum Z i) + (∑ i ∈ Iᶜ, rowSum Z i) = k - x := by
    simpa only [Finset.sum_add_sum_compl, totalMass, rowSum] using hmass
  have hrowcap : (∑ i ∈ Iᶜ, rowSum Z i) ≤ Iᶜ.card := by
    calc
      _ ≤ ∑ _i ∈ Iᶜ, (1 : ℝ) := Finset.sum_le_sum fun i _ => hr i
      _ = _ := by simp
  have hcolcap : (∑ j ∈ Jᶜ, colSum Z j) ≤ Jᶜ.card := by
    calc
      _ ≤ ∑ _j ∈ Jᶜ, (1 : ℝ) := Finset.sum_le_sum fun j _ => hc j
      _ = _ := by simp
  have hcols := cutMass_add_compl_rows Z I Jᶜ
  have hsplit := cutMass_add_compl_cols Z I J
  have hnonneg := cutMass_nonneg hZ Iᶜ Jᶜ
  have hI : (I.card : ℝ) + Iᶜ.card = k := by exact_mod_cast (show I.card + Iᶜ.card = k by simp)
  have hJ : (J.card : ℝ) + Jᶜ.card = k := by exact_mod_cast (show J.card + Jᶜ.card = k by simp)
  linarith

/-- All finite real transport cuts for the common demand `1 - x`. -/
theorem substochastic_transportCuts {k : ℕ} (Z : Board k k)
    (hZ : ∀ i j, 0 ≤ Z i j) (hr : ∀ i, rowSum Z i ≤ 1)
    (hc : ∀ j, colSum Z j ≤ 1) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hmass : totalMass Z = k - x) : TransportCuts Z (1 - x) := by
  intro I J
  by_cases hh : (I.card : ℝ) + J.card - k ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) hh).trans (cutMass_nonneg hZ I J)
  · have hnat : k < I.card + J.card := by
      exact_mod_cast (show (k : ℝ) < (I.card : ℝ) + J.card by linarith)
    have hreal : (k : ℝ) + 1 ≤ (I.card : ℝ) + J.card := by exact_mod_cast hnat
    have hcut := substochastic_cut_lower Z hZ hr hc x hmass I J
    nlinarith

/-- The exact substochastic permanent floor. Empty dimensions and zero entries
are included; the dependence on missing mass is a power, not a linear bound. -/
theorem permanent_lower_bound_of_substochastic {k : ℕ} (Z : Board k k)
    (hZ : ∀ i j, 0 ≤ Z i j) (hr : ∀ i, rowSum Z i ≤ 1)
    (hc : ∀ j, colSum Z j ≤ 1) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hmass : totalMass Z = k - x) :
    dittertConstant k * (1 - x) ^ k ≤ Z.permanent := by
  obtain ⟨B, hB, hBZ⟩ := exists_doublyStochastic_dominated_of_cuts hZ
    (show 0 ≤ 1 - x by linarith) (substochastic_transportCuts Z hZ hr hc x hx0 hx1 hmass)
  have hper := permanent_lower_bound_of_doublyStochastic hB
  calc
    _ ≤ (1 - x) ^ k * B.permanent := by
      have := mul_le_mul_of_nonneg_left hper (pow_nonneg (show 0 ≤ 1 - x by linarith) k)
      simpa only [mul_comm] using this
    _ = ((1 - x) • B).permanent := by rw [Matrix.permanent_smul, Fintype.card_fin]
    _ ≤ Z.permanent := permanent_mono
      (fun i j => mul_nonneg (by linarith) (nonneg_of_mem_doublyStochastic hB)) hBZ

/-- Independent bijections of the row and column labels preserve the permanent. -/
theorem permanent_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℝ) (er ec : ι ≃ κ) :
    (A.submatrix er ec).permanent = A.permanent := by
  have h := Matrix.permanent_permute_rows (ec.trans er.symm) (A.submatrix er er)
  have hsame : (A.submatrix er er).permanent = A.permanent :=
    permanent_reindex A er.symm
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using h.trans hsame

/-- The substochastic bound transported to any finite index type. -/
theorem permanent_lower_bound_of_substochastic_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Matrix ι ι ℝ)
    (hZ : ∀ i j, 0 ≤ Z i j) (hr : ∀ i, ∑ j, Z i j ≤ 1)
    (hc : ∀ j, ∑ i, Z i j ≤ 1) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hmass : ∑ i, ∑ j, Z i j = Fintype.card ι - x) :
    dittertConstant (Fintype.card ι) * (1 - x) ^ Fintype.card ι ≤ Z.permanent := by
  let e := (Fintype.equivFin ι).symm
  have hrow (i) : rowSum (Z.submatrix e e) i ≤ 1 := by
    simpa only [rowSum, Matrix.submatrix_apply, Equiv.sum_comp] using hr (e i)
  have hcol (j) : colSum (Z.submatrix e e) j ≤ 1 := by
    change (∑ i, Z (e i) (e j)) ≤ 1
    rw [Equiv.sum_comp e (fun i => Z i (e j))]
    exact hc (e j)
  have htotal : totalMass (Z.submatrix e e) = Fintype.card ι - x := by
    change (∑ i, ∑ j, Z (e i) (e j)) = _
    calc
      _ = ∑ i, ∑ j, Z (e i) j := Finset.sum_congr rfl (fun i _ => Equiv.sum_comp e (fun j => Z (e i) j))
      _ = ∑ i, ∑ j, Z i j := Equiv.sum_comp e (fun i => ∑ j, Z i j)
      _ = _ := hmass
  have h := permanent_lower_bound_of_substochastic (Z.submatrix e e)
    (fun i j => hZ (e i) (e j)) hrow hcol x hx0 hx1 htotal
  simpa only [permanent_submatrix_equiv] using h

/-- A square block with arbitrary, independently labeled row and column subsets. -/
def squareCutBlock {n : ℕ} (A : Board n n) (I J : Finset (Fin n))
    (e : I ≃ J) : Matrix I I ℝ := fun i j => A i (e j)

theorem squareCutBlock_sum_row {n : ℕ} (A : Board n n) (I J : Finset (Fin n))
    (e : I ≃ J) (i : I) : ∑ j, squareCutBlock A I J e i j = ∑ j ∈ J, A i j := by
  unfold squareCutBlock
  rw [Equiv.sum_comp e (fun j : J => A i j), Finset.sum_coe_sort]

theorem squareCutBlock_sum_col {n : ℕ} (A : Board n n) (I J : Finset (Fin n))
    (e : I ≃ J) (j : I) : ∑ i, squareCutBlock A I J e i j = ∑ i ∈ I, A i (e j) :=
  Finset.sum_coe_sort I (fun i => A i (e j))

theorem squareCutBlock_totalMass {n : ℕ} (A : Board n n) (I J : Finset (Fin n))
    (e : I ≃ J) : ∑ i, ∑ j, squareCutBlock A I J e i j = cutMass A I J := by
  simp_rw [squareCutBlock_sum_row]
  exact Finset.sum_coe_sort I (fun i => ∑ j ∈ J, A i j)

/-- The diagonal block of a doubly stochastic matrix is doubly substochastic. -/
theorem squareCutBlock_substochastic {n : ℕ} {B : Board n n}
    (hB : B ∈ doublyStochastic ℝ (Fin n)) (I J : Finset (Fin n)) (e : I ≃ J) :
    (∀ i j, 0 ≤ squareCutBlock B I J e i j) ∧
    (∀ i, ∑ j, squareCutBlock B I J e i j ≤ 1) ∧
    (∀ j, ∑ i, squareCutBlock B I J e i j ≤ 1) := by
  refine ⟨fun i j => nonneg_of_mem_doublyStochastic hB, ?_, ?_⟩
  · intro i
    rw [squareCutBlock_sum_row]
    calc
      _ ≤ ∑ j, B i j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
        (fun j _ _ => nonneg_of_mem_doublyStochastic hB)
      _ = 1 := sum_row_of_mem_doublyStochastic hB i
  · intro j
    rw [squareCutBlock_sum_col]
    calc
      _ ≤ ∑ i, B i (e j) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
        (fun i _ _ => nonneg_of_mem_doublyStochastic hB)
      _ = 1 := sum_col_of_mem_doublyStochastic hB (e j)

/-- A finite set and its complement give an actual partition equivalence. -/
def finsetSumCompl {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α) :
    I ⊕ ↥(Iᶜ) ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun a := if h : a ∈ I then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, Finset.mem_compl.mpr h⟩
  left_inv := by
    intro a
    cases a with
    | inl a => simp [a.property]
    | inr a => simp [Finset.mem_compl.mp a.property]
  right_inv := by intro a; dsimp; split_ifs <;> rfl

/-- Keeping arbitrary equal-cardinality diagonal blocks can only lower the permanent. -/
theorem permanent_squareCutBlocks_le {n : ℕ} (A : Board n n) (hA : ∀ i j, 0 ≤ A i j)
    (I J : Finset (Fin n)) (e : I ≃ J) (ec : ↥(Iᶜ) ≃ ↥(Jᶜ)) :
    (squareCutBlock A I J e).permanent * (squareCutBlock A Iᶜ Jᶜ ec).permanent ≤ A.permanent := by
  let er := finsetSumCompl I
  let eq := (e.sumCongr ec).trans (finsetSumCompl J)
  have h := permanent_diagonal_blocks_le (squareCutBlock A I J e)
    (fun (i : I) (j : ↥(Iᶜ)) => A i (ec j)) (fun (i : ↥(Iᶜ)) (j : I) => A i (e j)) (squareCutBlock A Iᶜ Jᶜ ec)
    (fun i j => hA i (e j)) (fun i j => hA i (ec j))
    (fun i j => hA i (e j)) (fun i j => hA i (ec j))
  have heq : Matrix.fromBlocks (squareCutBlock A I J e)
      (fun (i : I) (j : ↥(Iᶜ)) => A i (ec j)) (fun (i : ↥(Iᶜ)) (j : I) => A i (e j)) (squareCutBlock A Iᶜ Jᶜ ec) =
      A.submatrix er eq := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [heq, permanent_submatrix_equiv] at h
  exact h

/-- Equal row/column cut cardinalities force the two crossing block masses to agree. -/
theorem doublyStochastic_opposite_cutMass_eq {n : ℕ} {B : Board n n}
    (hB : B ∈ doublyStochastic ℝ (Fin n)) (I J : Finset (Fin n))
    (hcard : I.card = J.card) : cutMass B I Jᶜ = cutMass B Iᶜ J := by
  have hr := cutMass_add_compl_cols B I J
  have hc := cutMass_add_compl_rows B I J
  have hrow (i) : rowSum B i = 1 := sum_row_of_mem_doublyStochastic hB i
  have hcol (j) : colSum B j = 1 := sum_col_of_mem_doublyStochastic hB j
  simp only [hrow, hcol, Finset.sum_const, nsmul_eq_mul, mul_one] at hr hc
  rw [hcard] at hr
  linarith

/-- The two substochastic diagonal blocks give a lower bound for the actual
permanent, for arbitrary equal-cardinality subsets. -/
theorem permanent_lower_bound_of_diagonal_block_mass {n : ℕ} {B : Board n n}
    (hB : B ∈ doublyStochastic ℝ (Fin n)) (I J : Finset (Fin n))
    (hcard : I.card = J.card) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hmass : cutMass B I Jᶜ = x) :
    dittertConstant I.card * dittertConstant (n - I.card) * (1 - x) ^ n ≤ B.permanent := by
  let e : I ≃ J := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hcard)
  let ec : ↥(Iᶜ) ≃ ↥(Jᶜ) := Fintype.equivOfCardEq (by simp [hcard])
  have hrow (i) : rowSum B i = 1 := sum_row_of_mem_doublyStochastic hB i
  have h1 : cutMass B I J = I.card - x := by
    have h := cutMass_add_compl_cols B I J
    simp only [hrow, Finset.sum_const, nsmul_eq_mul, mul_one, hmass] at h
    linarith
  have h2 : cutMass B Iᶜ Jᶜ = Iᶜ.card - x := by
    have h := cutMass_add_compl_cols B Iᶜ J
    rw [← doublyStochastic_opposite_cutMass_eq hB I J hcard, hmass] at h
    simp only [hrow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    linarith
  have hb1 := squareCutBlock_substochastic hB I J e
  have hb2 := squareCutBlock_substochastic hB Iᶜ Jᶜ ec
  have hp1 := permanent_lower_bound_of_substochastic_fintype (squareCutBlock B I J e)
    hb1.1 hb1.2.1 hb1.2.2 x hx0 hx1
    (by simpa only [squareCutBlock_totalMass, Fintype.card_coe] using h1)
  have hp2 := permanent_lower_bound_of_substochastic_fintype (squareCutBlock B Iᶜ Jᶜ ec)
    hb2.1 hb2.2.1 hb2.2.2 x hx0 hx1
    (by simpa only [squareCutBlock_totalMass, Fintype.card_coe] using h2)
  simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin] at hp1 hp2
  have hcardle : I.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ I
  have hprod := mul_le_mul hp1 hp2
    (show 0 ≤ dittertConstant (n - I.card) * (1 - x) ^ (n - I.card) by
      unfold dittertConstant; positivity)
    (permanent_nonneg hb1.1)
  have halg : (dittertConstant I.card * (1 - x) ^ I.card) *
      (dittertConstant (n - I.card) * (1 - x) ^ (n - I.card)) =
      dittertConstant I.card * dittertConstant (n - I.card) * (1 - x) ^ n := by
    calc
      _ = dittertConstant I.card * dittertConstant (n - I.card) *
          ((1 - x) ^ I.card * (1 - x) ^ (n - I.card)) := by ring
      _ = dittertConstant I.card * dittertConstant (n - I.card) * (1 - x) ^ (I.card + (n - I.card)) := by rw [pow_add]
      _ = _ := by rw [Nat.add_sub_of_le hcardle]
  rw [halg] at hprod
  exact hprod.trans (permanent_squareCutBlocks_le B (fun i j => nonneg_of_mem_doublyStochastic hB) I J e ec)

/-- The near-block permanent floor, including arbitrary row and column subsets.
The crossing mass is the sum of both off-diagonal rectangles. -/
theorem permanent_lower_bound_of_two_blocks {n : ℕ} (A B : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hB : B ∈ doublyStochastic ℝ (Fin n))
    (q : ℝ) (hq : 0 < q) (hdom : ∀ i j, q * B i j ≤ A i j)
    (I J : Finset (Fin n)) (hcard : I.card = J.card) (w : ℝ)
    (hcross : cutMass A I Jᶜ + cutMass A Iᶜ J ≤ w) (hw : w < 2 * q) :
    dittertConstant I.card * dittertConstant (n - I.card) * (q - w / 2) ^ n ≤ A.permanent := by
  have hw0 : 0 ≤ w := (add_nonneg (cutMass_nonneg hA I Jᶜ) (cutMass_nonneg hA Iᶜ J)).trans hcross
  have hbase : 0 ≤ q - w / 2 := by linarith
  let x := cutMass B I Jᶜ
  have hx0 : 0 ≤ x := cutMass_nonneg (fun i j => nonneg_of_mem_doublyStochastic hB) I Jᶜ
  have hqx : 2 * q * x ≤ w := by
    have hleft := cutMass_mono (A := fun i j => q * B i j) hdom I Jᶜ
    have hright := cutMass_mono (A := fun i j => q * B i j) hdom Iᶜ J
    have heq := doublyStochastic_opposite_cutMass_eq hB I J hcard
    have hs (K L : Finset (Fin n)) : cutMass (fun i j => q * B i j) K L = q * cutMass B K L := by
      simp only [cutMass, Finset.mul_sum]
    rw [hs] at hleft hright
    rw [← heq] at hright
    change q * x ≤ _ at hleft hright
    linarith
  have hx1 : x < 1 := by nlinarith
  have hper := permanent_lower_bound_of_diagonal_block_mass hB I J hcard x hx0 hx1 rfl
  have hgamma : 0 ≤ dittertConstant I.card * dittertConstant (n - I.card) := by
    unfold dittertConstant; positivity
  calc
    _ ≤ dittertConstant I.card * dittertConstant (n - I.card) * (q * (1 - x)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase
        (by nlinarith : q - w / 2 ≤ q * (1 - x)) n) hgamma
    _ = q ^ n * (dittertConstant I.card * dittertConstant (n - I.card) * (1 - x) ^ n) := by
      rw [mul_pow]; ring
    _ ≤ q ^ n * B.permanent := mul_le_mul_of_nonneg_left hper (pow_nonneg hq.le n)
    _ = (q • B).permanent := by rw [Matrix.permanent_smul, Fintype.card_fin]
    _ ≤ A.permanent := permanent_mono
      (fun i j => mul_nonneg hq.le (nonneg_of_mem_doublyStochastic hB)) hdom

end DittertRybin
