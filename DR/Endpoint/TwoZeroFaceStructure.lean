import DR.Endpoint.PermanentFaceAveraging
import DR.Endpoint.PermanentFaceCompact

/-! A least-norm minimum on the actual two-zero face has identical ordinary
rows and columns. No optimizer form is assumed. -/

namespace DittertRybin
open scoped BigOperators

theorem LeastNormPermanentFaceMinimum.equal_rows {n : ℕ}
    {allowed : Fin (n+2) → Fin (n+2) → Prop} {A : Board (n+2) (n+2)}
    (hmin : LeastNormPermanentFaceMinimum allowed A)
    (hcofactor : ∀ i j, allowed i j → A.permanent ≤ permanentalCofactor A i j)
    (a b : Fin (n+2)) (hrows : ∀ j, allowed a j ↔ allowed b j) : A a = A b := by
  by_cases hab : a = b
  · rw [hab]
  have hfeas := averagePermanentRows_mem_face hmin.1.1 hmin.1.2.1 a b hab hrows
  have hvalue := hmin.1.average_rows_permanent hcofactor a b hab hrows
  have havg : PermanentFaceMinimum allowed (averagePermanentRows A a b) :=
    ⟨hfeas.1,hfeas.2,fun B hB hz => hvalue.trans_le (hmin.1.2.2 B hB hz)⟩
  have hnorm := hmin.2 _ havg
  rw [averagePermanentRows_norm A a b hab] at hnorm
  have hsum0 : 0 ≤ ∑ j, (A a j-A b j)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsum : (∑ j, (A a j-A b j)^2) = 0 := by linarith
  funext j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => sq_nonneg (A a j-A b j))).mp hsum j (Finset.mem_univ j)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hj)

theorem twoZeroAllowed_symmetric {n : ℕ} (i j : Fin (n+2)) :
    twoZeroAllowed n i j ↔ twoZeroAllowed n j i := by
  unfold twoZeroAllowed
  tauto

theorem LeastNormPermanentFaceMinimum.twoZero_transpose {n : ℕ}
    {A : Board (n+2) (n+2)} (hA : LeastNormPermanentFaceMinimum (twoZeroAllowed n) A) :
    LeastNormPermanentFaceMinimum (twoZeroAllowed n) A.transpose := by
  have h := hA.transpose
  have heq : (fun i j => twoZeroAllowed n j i) = twoZeroAllowed n := by
    funext i j
    exact propext (twoZeroAllowed_symmetric j i)
  rwa [heq] at h

theorem twoZeroAllowed_ordinary {n : ℕ} (i : Fin n) (j : Fin (n+2)) :
    twoZeroAllowed n i.succ.succ j := by
  simp [twoZeroAllowed, ← Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one']

theorem LeastNormPermanentFaceMinimum.twoZero_ordinary_rows {n : ℕ} (hn : 0 < n)
    {A : Board (n+2) (n+2)} (hA : LeastNormPermanentFaceMinimum (twoZeroAllowed n) A)
    (i k : Fin n) : A i.succ.succ = A k.succ.succ :=
  hA.equal_rows (fun a b hab => hA.1.twoZero_allowed_cofactor_ge hn a b hab)
    _ _ (fun j => iff_of_true (twoZeroAllowed_ordinary i j) (twoZeroAllowed_ordinary k j))

theorem LeastNormPermanentFaceMinimum.twoZero_ordinary_columns {n : ℕ} (hn : 0 < n)
    {A : Board (n+2) (n+2)} (hA : LeastNormPermanentFaceMinimum (twoZeroAllowed n) A)
    (i k : Fin n) (j : Fin (n+2)) : A j i.succ.succ = A j k.succ.succ :=
  congrFun (hA.twoZero_transpose.twoZero_ordinary_rows hn i k) j

theorem exists_twoZero_leastNorm_minimum (n : ℕ) :
    ∃ A : Board (n+2) (n+2), LeastNormPermanentFaceMinimum (twoZeroAllowed n) A :=
  exists_leastNormPermanentFaceMinimum
    ⟨twoZeroCompetitor n,twoZeroCompetitor_mem_doublyStochastic n,twoZeroCompetitor_on_face n⟩

end DittertRybin
