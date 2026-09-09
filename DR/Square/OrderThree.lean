import DR.Compactness
import DR.Square.Contenders
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Order-three Dittert prerequisites

This module develops the exact cubic and full-simplex variation identities
for the endpoint support proof. No support classification or order-three
maximization theorem is assumed.
-/

open scoped BigOperators Topology
open Finset Set Filter

namespace DittertRybin

private theorem sum_perm_fin_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℝ) :
    (∑ σ, f σ) = ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, τ)) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm f, Fintype.sum_prod_type]

theorem permanent_three (A : Board 3 3) :
    A.permanent = A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 2 1 * A 1 2 +
      A 1 0 * A 0 1 * A 2 2 + A 1 0 * A 2 1 * A 0 2 +
      A 2 0 * A 0 1 * A 1 2 + A 2 0 * A 1 1 * A 0 2 := by
  rw [Matrix.permanent, sum_perm_fin_succ]
  simp_rw [sum_perm_fin_succ (n := 1), sum_perm_fin_succ (n := 0)]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, Equiv.swap_apply_def]
  ring

/-- The complementary pair product for a row in the three-row cubic. -/
noncomputable def orderThreePair (A : Board 3 3) (i : Fin 3) : ℝ :=
  ∑ j, A (i + 1) j * A (i + 2) j

/-- The exact derivative of the cubic, defined at every cell including zeros. -/
noncomputable def orderThreeGradient (A : Board 3 3) (i j : Fin 3) : ℝ :=
  colSum A (j + 1) * colSum A (j + 2) + orderThreePair A i +
    rowSum A (i + 1) * A (i + 2) j + rowSum A (i + 2) * A (i + 1) j -
      2 * A (i + 1) j * A (i + 2) j

theorem dittert_three_cubic (A : Board 3 3) :
    dittertFunctional A =
      colSum A 0 * colSum A 1 * colSum A 2 +
      ∑ i, rowSum A i * orderThreePair A i - 2 * ∑ j, A 0 j * A 1 j * A 2 j := by
  rw [dittertFunctional, permanent_three]
  simp [rowSum, colSum, orderThreePair, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

private noncomputable def cubicThree {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) : R :=
  (∑ i, A i 0) * (∑ i, A i 1) * (∑ i, A i 2) +
    ∑ i, (∑ j, A i j) * (∑ j, A (i + 1) j * A (i + 2) j) -
      2 * ∑ j, A 0 j * A 1 j * A 2 j

private theorem cubicThree_eq_dittert (A : Board 3 3) : cubicThree A = dittertFunctional A := by
  exact (dittert_three_cubic A).symm

/-- The actual derivative along any affine matrix line, without positivity assumptions. -/
theorem hasDerivAt_dittert_three_line (A D : Board 3 3) :
    HasDerivAt (fun t : ℝ => dittertFunctional (fun i j => A i j + D i j * t))
      (∑ i, ∑ j, orderThreeGradient A i j * D i j) 0 := by
  let Q : Polynomial ℝ := cubicThree (fun i j => Polynomial.C (A i j) + Polynomial.C (D i j) * Polynomial.X)
  have heval (t : ℝ) : Q.eval t = dittertFunctional (fun i j => A i j + D i j * t) := by
    calc
      _ = cubicThree (fun i j => A i j + D i j * t) := by
        simp [Q, cubicThree, Polynomial.eval_finsetSum]
      _ = _ := cubicThree_eq_dittert _
  have hderiv : Q.derivative.eval 0 = ∑ i, ∑ j, orderThreeGradient A i j * D i j := by
    simp [Q, cubicThree, orderThreeGradient, orderThreePair, rowSum, colSum,
      Fin.sum_univ_succ, Polynomial.derivative_mul]
    ring
  simpa only [heval, hderiv] using Q.hasDerivAt 0

/-- Transfer one unit of infinitesimal mass from cell v to cell u. -/
def cellTransferDirection {m n : ℕ} (u v : Fin m × Fin n) : Board m n :=
  fun i j => (if (i, j) = u then 1 else 0) - (if (i, j) = v then 1 else 0)

theorem cellTransferDirection_totalMass {m n : ℕ} (u v : Fin m × Fin n) :
    totalMass (cellTransferDirection u v) = 0 := by
  rcases u with ⟨ui, uj⟩
  rcases v with ⟨vi, vj⟩
  simp [cellTransferDirection, totalMass, rowSum, Finset.sum_sub_distrib, Prod.mk.injEq, ite_and]

theorem hasDerivAt_dittert_three_cellTransfer (A : Board 3 3) (u v : Fin 3 × Fin 3) :
    HasDerivAt (fun t : ℝ => dittertFunctional
      (fun i j => A i j + cellTransferDirection u v i j * t))
      (orderThreeGradient A u.1 u.2 - orderThreeGradient A v.1 v.2) 0 := by
  have h := hasDerivAt_dittert_three_line A (cellTransferDirection u v)
  rcases u with ⟨ui, uj⟩
  rcases v with ⟨vi, vj⟩
  simpa [cellTransferDirection, mul_sub, Finset.sum_sub_distrib, Prod.mk.injEq, ite_and] using h

theorem cellTransfer_feasible {m n : ℕ} {A : Board m n} (hA : ∀ i j, 0 ≤ A i j)
    (u v : Fin m × Fin n) {t : ℝ} (ht : 0 ≤ t) (htv : t ≤ A v.1 v.2) :
    (∀ i j, 0 ≤ A i j + cellTransferDirection u v i j * t) ∧
      totalMass (fun i j => A i j + cellTransferDirection u v i j * t) = totalMass A := by
  constructor
  · intro i j
    unfold cellTransferDirection
    split_ifs with hu hv hv
    · simpa using hA i j
    · simpa using add_nonneg (hA i j) ht
    · have hv' : A i j = A v.1 v.2 := by cases hv; rfl
      simp only [zero_sub, one_mul, neg_mul, one_mul]
      linarith
    · simpa using hA i j
  · have hzero := cellTransferDirection_totalMass u v
    simp only [totalMass, rowSum, Finset.sum_add_distrib, ← Finset.sum_mul] at hzero ⊢
    rw [hzero]
    ring

private theorem deriv_nonpos_of_right_max {f : ℝ → ℝ} {d ε : ℝ}
    (hε : 0 < ε) (hd : HasDerivAt f d 0) (hmax : ∀ t, 0 < t → t < ε → f t ≤ f 0) :
    d ≤ 0 := by
  have hlim := hd.tendsto_slope_zero_right
  apply le_of_tendsto hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < ε :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hte
  simpa [div_eq_mul_inv, mul_comm] using div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hmax t ht hte)) ht.le

/-- Full-simplex first-order inequality: every cell's gradient is bounded by
that of each positive donor cell. Missing target cells are included. -/
theorem dittert_three_globalMax_gradient_le {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (u v : Fin 3 × Fin 3) (hv : 0 < A v.1 v.2) :
    orderThreeGradient A u.1 u.2 ≤ orderThreeGradient A v.1 v.2 := by
  have h := deriv_nonpos_of_right_max hv (hasDerivAt_dittert_three_cellTransfer A u v) (by
    intro t ht htv
    obtain ⟨hpos, hmass'⟩ := cellTransfer_feasible hA u v ht.le htv.le
    have h := hmax _ hpos (hmass'.trans hmass)
    simpa using h)
  linarith

theorem dittert_three_globalMax_gradient_eq {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (u v : Fin 3 × Fin 3) (hu : 0 < A u.1 u.2) (hv : 0 < A v.1 v.2) :
    orderThreeGradient A u.1 u.2 = orderThreeGradient A v.1 v.2 :=
  le_antisymm (dittert_three_globalMax_gradient_le hA hmass hmax u v hv)
    (dittert_three_globalMax_gradient_le hA hmass hmax v u hu)

/-- Row mass in columns other than the selected physical pair. -/
def orderThreeRemainingRow (A : Board 3 3) (j k i : Fin 3) : ℝ :=
  ∑ l, if l = j ∨ l = k then 0 else A i l

def orderThreeColumnComparison (A : Board 3 3) (j k i h : Fin 3) : ℝ :=
  if i = h then ∑ r, orderThreeRemainingRow A j k r
  else orderThreeRemainingRow A j k i + orderThreeRemainingRow A j k h

/-- Exact physical-column gradient difference, valid on every boundary support. -/
theorem orderThree_column_gradient_difference (A : Board 3 3) (i j k : Fin 3) (hjk : j ≠ k) :
    orderThreeGradient A i j - orderThreeGradient A i k =
      -(∑ h, orderThreeColumnComparison A j k i h * (A h j - A h k)) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [orderThreeGradient, orderThreePair, orderThreeColumnComparison,
      orderThreeRemainingRow, rowSum, colSum, Fin.sum_univ_succ] <;> ring

theorem orderThree_column_comparison_nonneg {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (i j k : Fin 3) (hjk : j ≠ k) (hik : 0 < A i k) :
    0 ≤ ∑ h, orderThreeColumnComparison A j k i h * (A h j - A h k) := by
  have h := dittert_three_globalMax_gradient_le hA hmass hmax (i, j) (i, k) hik
  have hid := orderThree_column_gradient_difference A i j k hjk
  dsimp at h
  linarith

theorem orderThree_column_comparison_eq_zero {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (i j k : Fin 3) (hjk : j ≠ k) (hij : 0 < A i j) (hik : 0 < A i k) :
    (∑ h, orderThreeColumnComparison A j k i h * (A h j - A h k)) = 0 := by
  have h := dittert_three_globalMax_gradient_eq hA hmass hmax (i, j) (i, k) hij hik
  have hid := orderThree_column_gradient_difference A i j k hjk
  dsimp at h
  linarith

/-- A simultaneous blend of two columns; the total in each row is preserved. -/
def blendThreeColumns (A : Board 3 3) (j k : Fin 3) (t : ℝ) : Board 3 3 :=
  fun i l => if l = j then (1 - t) * A i j + t * A i k
    else if l = k then t * A i j + (1 - t) * A i k else A i l

theorem blendThreeColumns_zero (A : Board 3 3) (j k : Fin 3) : blendThreeColumns A j k 0 = A := by
  ext i l
  simp only [blendThreeColumns, sub_zero, one_mul, zero_mul, add_zero, zero_add]
  split_ifs <;> subst_vars <;> rfl

theorem blendThreeColumns_feasible {A : Board 3 3} (hA : ∀ i l, 0 ≤ A i l)
    (j k : Fin 3) (hjk : j ≠ k) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (∀ i l, 0 ≤ blendThreeColumns A j k t i l) ∧
      totalMass (blendThreeColumns A j k t) = totalMass A := by
  constructor
  · intro i l
    unfold blendThreeColumns
    split_ifs
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hA i j)) (mul_nonneg ht.1 (hA i k))
    · exact add_nonneg (mul_nonneg ht.1 (hA i j)) (mul_nonneg (sub_nonneg.mpr ht.2) (hA i k))
    · exact hA i l
  · fin_cases j <;> fin_cases k <;> simp_all [totalMass, rowSum, blendThreeColumns, Fin.sum_univ_succ] <;> ring

/-- Separate column multilinearity gives this exact quadratic identity. -/
theorem dittert_three_column_blend (A : Board 3 3) (j k : Fin 3) (hjk : j ≠ k) (t : ℝ) :
    dittertFunctional (blendThreeColumns A j k t) = dittertFunctional A +
      t * (1 - t) * ∑ i, (orderThreeGradient A i j - orderThreeGradient A i k) * (A i k - A i j) := by
  simp_rw [dittert_three_cubic]
  fin_cases j <;> fin_cases k <;>
    simp_all [rowSum, colSum, orderThreePair, orderThreeGradient, blendThreeColumns, Fin.sum_univ_succ] <;> ring

/-- Equal-support column averaging is flat at an actual global maximizer.
This asserts no monotonicity for an arbitrary input matrix. -/
theorem dittert_three_same_support_blend_flat {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (j k : Fin 3) (hjk : j ≠ k) (hsupport : ∀ i, 0 < A i j ↔ 0 < A i k) (t : ℝ) :
    dittertFunctional (blendThreeColumns A j k t) = dittertFunctional A := by
  rw [dittert_three_column_blend A j k hjk]
  have hsum : (∑ i, (orderThreeGradient A i j - orderThreeGradient A i k) * (A i k - A i j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hp : 0 < A i j
    · have hgrad := dittert_three_globalMax_gradient_eq hA hmass hmax (i, j) (i, k) hp ((hsupport i).mp hp)
      rw [hgrad, sub_self, zero_mul]
    · have hij : A i j = 0 := le_antisymm (le_of_not_gt hp) (hA i j)
      have hik : A i k = 0 := le_antisymm (le_of_not_gt (mt (hsupport i).mpr hp)) (hA i k)
      simp [hij, hik]
  rw [hsum]
  ring

/-- Schur elimination for two proper columns, with all boundary row remainders allowed. -/
theorem orderThree_proper_pair_schur {a b e f x y z : ℝ}
    (hE : 0 < x + y + z)
    (hcommon : -(x + z) * e + (y + z) * b + (x + y + z) * (a - f) = 0)
    (hleft : 0 ≤ -(x + y + z) * e + (x + y) * b + (x + z) * (a - f))
    (hright : -(x + y) * e + (x + y + z) * b + (y + z) * (a - f) ≤ 0) :
    e * y * (2 * (x + y + z) - y) ≤ b * (x ^ 2 + x * y + y ^ 2 - z ^ 2) ∧
      b * x * (2 * (x + y + z) - x) ≤ e * (x ^ 2 + x * y + y ^ 2 - z ^ 2) := by
  have h0 := congrArg (fun q : ℝ => (x + z) * q) hcommon
  have h1 := congrArg (fun q : ℝ => (y + z) * q) hcommon
  have hL := mul_nonneg hE.le hleft
  have hR := mul_nonpos_of_nonneg_of_nonpos hE.le hright
  constructor <;> nlinarith [h0, h1, hL, hR]

theorem orderThree_proper_pair_D_pos {b e x y z : ℝ}
    (hb : 0 < b) (he : 0 < e) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hE : 0 < x + y + z)
    (hleft : e * y * (2 * (x + y + z) - y) ≤ b * (x ^ 2 + x * y + y ^ 2 - z ^ 2))
    (hright : b * x * (2 * (x + y + z) - x) ≤ e * (x ^ 2 + x * y + y ^ 2 - z ^ 2)) :
    0 < x ^ 2 + x * y + y ^ 2 - z ^ 2 := by
  by_cases hxp : 0 < x
  · have hp := mul_pos (mul_pos hb hxp) (show 0 < 2 * (x + y + z) - x by linarith)
    nlinarith
  by_cases hyp : 0 < y
  · have hp := mul_pos (mul_pos he hyp) (show 0 < 2 * (x + y + z) - y by linarith)
    nlinarith
  have hx0 : x = 0 := le_antisymm (le_of_not_gt hxp) hx
  have hy0 : y = 0 := le_antisymm (le_of_not_gt hyp) hy
  subst x
  subst y
  have hzp : 0 < z := by simpa using hE
  have hprod := mul_pos hb (sq_pos_of_pos hzp)
  norm_num at hleft
  nlinarith

/-- The direction of the exclusive-entry ordering follows the remainder ordering. -/
theorem orderThree_proper_pair_entry_order {b e x y z : ℝ}
    (hb : 0 < b) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxy : y < x)
    (hD : 0 < x ^ 2 + x * y + y ^ 2 - z ^ 2)
    (hright : b * x * (2 * (x + y + z) - x) ≤ e * (x ^ 2 + x * y + y ^ 2 - z ^ 2)) :
    b ≤ e := by
  have hdiff : x ^ 2 + x * y + y ^ 2 - z ^ 2 ≤ x * (2 * (x + y + z) - x) := by
    have hyy := mul_nonpos_of_nonneg_of_nonpos hy (show y - x ≤ 0 by linarith)
    have hzz := mul_nonneg hz (show 0 ≤ 2 * x + z by linarith)
    nlinarith
  have h := mul_le_mul_of_nonneg_left hdiff hb.le
  exact (mul_le_mul_iff_left₀ hD).mp (h.trans (by simpa [mul_assoc] using hright))

theorem orderThree_proper_pair_quartic {b e x y z : ℝ}
    (hb : 0 < b) (he : 0 < e) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hD : 0 < x ^ 2 + x * y + y ^ 2 - z ^ 2)
    (hleft : e * y * (2 * (x + y + z) - y) ≤ b * (x ^ 2 + x * y + y ^ 2 - z ^ 2))
    (hright : b * x * (2 * (x + y + z) - x) ≤ e * (x ^ 2 + x * y + y ^ 2 - z ^ 2)) :
    x * y * (2 * (x + y + z) - x) * (2 * (x + y + z) - y) ≤
      (x ^ 2 + x * y + y ^ 2 - z ^ 2) ^ 2 := by
  have hprod := mul_le_mul hleft hright
    (mul_nonneg (mul_nonneg hb.le hx) (by linarith))
    (mul_pos hb hD).le
  apply (mul_le_mul_iff_right₀ (mul_pos hb he)).mp
  convert hprod using 1 <;> ring

/-- Positive remaining masses force a strict majority in one omitted row.
The polynomial certificate also covers the triangle boundary exactly. -/
theorem orderThree_proper_pair_majority {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : y ≤ x)
    (hD : 0 < x ^ 2 + x * y + y ^ 2 - z ^ 2)
    (hq : x * y * (2 * (x + y + z) - x) * (2 * (x + y + z) - y) ≤
      (x ^ 2 + x * y + y ^ 2 - z ^ 2) ^ 2) : y + z < x := by
  by_contra hnot
  have htri : x ≤ y + z := le_of_not_gt hnot
  have hzlt : z < x + y := by
    by_contra hn
    have hzz := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn))
      (show 0 ≤ z + (x + y) by linarith)
    nlinarith [mul_pos hx hy]
  let a := (x + z - y) / 2
  let b := (x + y - z) / 2
  let c := (y + z - x) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  let D := 6*a^2*b + 6*a^2*c + 6*a*b^2 + 20*a*b*c + 6*a*c^2 + 6*b^2*c + 6*b*c^2
  have hDp : 0 < D := by dsimp [D]; positivity
  have hid : (x ^ 2 + x * y + y ^ 2 - z ^ 2) ^ 2 -
      x * y * (2 * (x + y + z) - x) * (2 * (x + y + z) - y) =
        -(x + y + z) * D := by
    dsimp [D, a, b, c]
    ring
  have hpos := mul_pos (show 0 < x + y + z by linarith) hDp
  nlinarith

/-- Two different doubleton supports and a full column, in a fixed axis order. -/
def orderThreeTwoProperBoard (a b e f x y z : ℝ) : Board 3 3 :=
  ![![0, e, x], ![a, f, z], ![b, 0, y]]

/-- The two-doubleton-plus-full support pattern cannot satisfy the actual
simplex first-order inequalities. Every displayed nonzero entry is positive. -/
theorem orderThree_two_proper_not_stationary {a b e f x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hf : 0 < f)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hcommon : orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 1 0 =
      orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 1 1)
    (hleft : orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 0 0 ≤
      orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 0 1)
    (hright : orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 2 1 ≤
      orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 2 0)
    (hmiss0 : orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 0 0 ≤
      orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 2 0)
    (hmiss2 : orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 2 1 ≤
      orderThreeGradient (orderThreeTwoProperBoard a b e f x y z) 0 1) : False := by
  norm_num [orderThreeGradient, orderThreePair, orderThreeTwoProperBoard,
    rowSum, colSum, Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hcommon hleft hright hmiss0 hmiss2
  have hE : 0 < x + y + z := by linarith
  obtain ⟨hL, hR⟩ := orderThree_proper_pair_schur (a := a) (b := b) (e := e)
    (f := f) (x := x) (y := y) (z := z) hE (by nlinarith) (by nlinarith) (by nlinarith)
  have hD := orderThree_proper_pair_D_pos hb he hx.le hy.le hz.le hE hL hR
  have hq := orderThree_proper_pair_quartic hb he hx.le hy.le hz.le hD hL hR
  rcases le_total y x with hxy | hyx
  · have hmajor := orderThree_proper_pair_majority hx hy hz hxy hD hq
    have hbe := orderThree_proper_pair_entry_order hb hy.le hz.le (by linarith) hD hR
    have h1 := mul_nonneg ha.le (sub_nonneg.mpr hbe)
    have h2 := mul_pos (show 0 < x + e - y - b by linarith) hf
    have h3 := mul_pos hz (show 0 < x - y + e by linarith)
    nlinarith
  · have hDs : 0 < y ^ 2 + y * x + x ^ 2 - z ^ 2 := by nlinarith
    have hqs : y * x * (2 * (y + x + z) - y) * (2 * (y + x + z) - x) ≤
        (y ^ 2 + y * x + x ^ 2 - z ^ 2) ^ 2 := by
      convert hq using 1 <;> ring
    have hmajor := orderThree_proper_pair_majority hy hx hz hyx hDs hqs
    have hRs : e * y * (2 * (y + x + z) - y) ≤ b * (y ^ 2 + y * x + x ^ 2 - z ^ 2) := by
      convert hL using 1 <;> ring
    have heb := orderThree_proper_pair_entry_order he hx.le hz.le (by linarith) hDs hRs
    have h1 := mul_nonneg hf.le (sub_nonneg.mpr heb)
    have h2 := mul_pos (show 0 < y + b - x - e by linarith) ha
    have h3 := mul_pos hz (show 0 < y - x + b by linarith)
    nlinarith

theorem orderThree_two_proper_not_globalMax {a b e f x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hf : 0 < f)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hmass : totalMass (orderThreeTwoProperBoard a b e f x y z) = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional (orderThreeTwoProperBoard a b e f x y z)) : False := by
  let A := orderThreeTwoProperBoard a b e f x y z
  have hA : ∀ i j, 0 ≤ A i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [A, orderThreeTwoProperBoard] <;> positivity
  apply orderThree_two_proper_not_stationary ha hb he hf hx hy hz
  · exact dittert_three_globalMax_gradient_eq hA hmass hmax (1, 0) (1, 1) ha hf
  · exact dittert_three_globalMax_gradient_le hA hmass hmax (0, 0) (0, 1) he
  · exact dittert_three_globalMax_gradient_le hA hmass hmax (2, 1) (2, 0) hb
  · exact dittert_three_globalMax_gradient_le hA hmass hmax (0, 0) (2, 0) hb
  · exact dittert_three_globalMax_gradient_le hA hmass hmax (2, 1) (0, 1) he

end DittertRybin
