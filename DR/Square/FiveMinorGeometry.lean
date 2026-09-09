import DR.Square.FiveMinorProducts
import DR.Square.MarginalCutOrder

/-! Exact conservation identities for the same actual cut used by both order-five branches. -/

namespace DittertRybin
open scoped BigOperators

theorem cut_block_mass_identities {n : ℕ} (A : Board n n)
    (I J : Finset (Fin n)) (s u v w M : ℝ)
    (hmass : totalMass A = M)
    (hr : (∑ i ∈ I, rowSum A i) = s-u)
    (hc : (∑ j ∈ J, colSum A j) = s+v)
    (hw : cutMass A I Jᶜ + cutMass A Iᶜ J = w) :
    cutMass A I Jᶜ = (w-u-v)/2 ∧
    cutMass A Iᶜ J = (w+u+v)/2 ∧
    cutMass A I J = s+(v-u-w)/2 ∧
    cutMass A Iᶜ Jᶜ = M-s+(u-v-w)/2 := by
  have hrow := cutMass_add_compl_cols A I J
  have hcol := cutMass_add_compl_rows A I J
  have hrowc := cutMass_add_compl_cols A Iᶜ J
  have hsum := Finset.sum_add_sum_compl I (rowSum A)
  change _ = totalMass A at hsum
  rw [hmass, hr] at hsum
  rw [hr] at hrow
  rw [hc] at hcol
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem lower_cut_defects_nonneg {n : ℕ} (hn : 0 < n) (A : Board n n)
    (I J : Finset (Fin n)) (horder : LowerMarginalCut A I J)
    (hmass : totalMass A = n) (s : ℕ) (hI : I.card = s) (hJ : J.card = s)
    (u v : ℝ) (hr : (∑ i ∈ I, rowSum A i) = s-u)
    (hc : (∑ j ∈ J, colSum A j) = s+v) : 0 ≤ u ∧ 0 ≤ v := by
  have h := horder.mass_orientation hn hmass
  rw [hI, hJ, hr, hc] at h
  constructor <;> linarith [h.1,h.2]

theorem crossing_ge_defect_sum {n : ℕ} (A : Board n n) (hA : ∀ i j, 0 ≤ A i j)
    (I J : Finset (Fin n)) (s u v w M : ℝ)
    (hmass : totalMass A = M) (hr : (∑ i ∈ I, rowSum A i) = s-u)
    (hc : (∑ j ∈ J, colSum A j) = s+v)
    (hw : cutMass A I Jᶜ + cutMass A Iᶜ J = w) : u+v ≤ w := by
  have he := (cut_block_mass_identities A I J s u v w M hmass hr hc hw).1
  have hh := cutMass_nonneg hA I Jᶜ
  rw [he] at hh
  linarith

end DittertRybin
