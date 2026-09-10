import DR.Endpoint.RowCollisionTwoClasses
import DR.Endpoint.RowPairMoments
import DR.Endpoint.RowCollisionBounds

/-! Localized exact collision-pattern loads. Increasing pairs make
the tripleton and second-doubleton counts unique. The first doubleton in
a two-doubleton term is the one containing the specified row. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def rowLocalizedDoubletonLoad {m n : ℕ} (X : Board m n) (i : Fin m) : ℝ :=
  ∑ e ∈ rowCollisionIncident i, rowDoubletonProbability X e/rowAvoidance X

noncomputable def rowLocalizedTripletonLoad {m n : ℕ} (X : Board m n) (i : Fin m) : ℝ :=
  ∑ e ∈ rowPairsOutside i, rowTripletonProbability X i e.val.1 e.val.2/rowAvoidance X

def rowPairsDisjoint {m : ℕ} (e : SampleIndexPair m) : Finset (SampleIndexPair m) :=
  Finset.univ.filter (fun f => Disjoint ({e.val.1,e.val.2} : Finset (Fin m)) {f.val.1,f.val.2})

noncomputable def rowLocalizedTwoDoubletonsLoad {m n : ℕ} (X : Board m n) (i : Fin m) : ℝ :=
  ∑ e ∈ rowCollisionIncident i, ∑ f ∈ rowPairsDisjoint e,
    rowTwoDoubletonsProbability X e f/rowAvoidance X

noncomputable def rowLocalizedDeficitTwoLoad {m n : ℕ} (X : Board m n) (i : Fin m) : ℝ :=
  rowLocalizedTripletonLoad X i+rowLocalizedTwoDoubletonsLoad X i

/-- Exact doubleton ratios sum to at most 16/9 times the local collision load. -/
theorem rowLocalizedDoubletonLoad_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (i : Fin m) :
    rowLocalizedDoubletonLoad X i ≤ (16/9)*rowCollisionLoad X i := by
  unfold rowLocalizedDoubletonLoad
  rw [← sum_rowCollisionIncident X i,Finset.mul_sum]
  exact Finset.sum_le_sum (fun e _ => rowDoubletonProbability_ratio_le X hX hs hd e)

/-- The unordered tripleton third moments retain the factor one half. -/
theorem rowTripleton_moment_sum_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (cap : ℝ) (hcap : ∀ u, colSum X u ≤ cap) (i : Fin m) :
    (∑ e ∈ rowPairsOutside i, ∑ u, X i u*X e.val.1 u*X e.val.2 u) ≤
      (cap/2)*rowCollisionLoad X i := by
  classical
  let s : Fin n → ℝ := fun u => ∑ h ∈ Finset.univ.erase i, X h u
  have hs0 (u : Fin n) : 0 ≤ s u := Finset.sum_nonneg (fun h _ => hX h u)
  have hsle (u : Fin n) : s u ≤ cap :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i _)
      (fun h _ _ => hX h u)).trans (hcap u)
  have hsid (u : Fin n) : s u=colSum X u-X i u :=
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  have hsum : (∑ u, X i u*s u)=rowCollisionLoad X i := by
    rw [rowCollisionLoad_eq X hs i]
    simp_rw [hsid]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ u, (cap/2)*(X i u*s u) := by
      apply Finset.sum_le_sum
      intro u hu
      have hp := sum_rowPairsOutside_product_le (fun h => X h u) i
      have hmul := mul_le_mul_of_nonneg_left hp (hX i u)
      have he : (∑ e ∈ rowPairsOutside i, X i u*X e.val.1 u*X e.val.2 u) =
          X i u*(∑ e ∈ rowPairsOutside i, X e.val.1 u*X e.val.2 u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        ring
      rw [he]
      have hn := mul_nonneg (hX i u) (mul_nonneg (hs0 u) (sub_nonneg.mpr (hsle u)))
      change _ ≤ X i u*((1/2)*(s u)^2) at hmul
      nlinarith
    _ = _ := by rw [← Finset.mul_sum,hsum]

theorem rowLocalizedTripletonLoad_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8)
    (cap : ℝ) (hcap : ∀ u, colSum X u ≤ cap) (i : Fin m) :
    rowLocalizedTripletonLoad X i ≤ (32/27)*cap*rowCollisionLoad X i := by
  have hp : rowLocalizedTripletonLoad X i ≤ (64/27)*
      (∑ e ∈ rowPairsOutside i, ∑ u, X i u*X e.val.1 u*X e.val.2 u) := by
    unfold rowLocalizedTripletonLoad
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    exact rowTripletonProbability_ratio_le X hX hs hd i e.val.1 e.val.2 hi.1.symm hi.2.symm (ne_of_lt e.property)
  apply hp.trans
  have h := mul_le_mul_of_nonneg_left (rowTripleton_moment_sum_le X hX hs cap hcap i)
    (show (0:ℝ) ≤ 64/27 by norm_num)
  apply h.trans_eq
  ring

theorem rowLocalizedTwoDoubletonsLoad_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (i : Fin m) :
    rowLocalizedTwoDoubletonsLoad X i ≤
      (256/81)*rowCollisionLoad X i*rowCollisionIntensity X := by
  have hsub (e : SampleIndexPair m) :
      (∑ f ∈ rowPairsDisjoint e, rowCollisionProbability X f.val.1 f.val.2) ≤ rowCollisionIntensity X := by
    rw [rowCollisionIntensity_eq_sum_edges]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun f _ _ => rowCollisionProbability_nonneg X hX _ _)
  have he (e : SampleIndexPair m) :
      (∑ f ∈ rowPairsDisjoint e, rowTwoDoubletonsProbability X e f/rowAvoidance X) ≤
        (256/81)*rowCollisionProbability X e.val.1 e.val.2*rowCollisionIntensity X := by
    calc
      _ ≤ ∑ f ∈ rowPairsDisjoint e,
          (256/81)*(rowCollisionProbability X e.val.1 e.val.2*rowCollisionProbability X f.val.1 f.val.2) := by
        apply Finset.sum_le_sum
        intro f hf
        exact rowTwoDoubletonsProbability_ratio_le X hX hs hd e f (Finset.mem_filter.mp hf).2
      _ = ((256/81)*rowCollisionProbability X e.val.1 e.val.2)*
          (∑ f ∈ rowPairsDisjoint e, rowCollisionProbability X f.val.1 f.val.2) := by
        simp_rw [← mul_assoc]
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsub e)
        (mul_nonneg (by norm_num) (rowCollisionProbability_nonneg X hX _ _))
  unfold rowLocalizedTwoDoubletonsLoad
  have h := Finset.sum_le_sum (fun e (_ : e ∈ rowCollisionIncident i) => he e)
  apply h.trans_eq
  rw [← Finset.sum_mul,← Finset.mul_sum,sum_rowCollisionIncident]

/-- The localized deficit-two estimate: every exact pattern involving i
appears once, with the tripleton half-factor retained. -/
theorem rowLocalizedDeficitTwoLoad_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8)
    (cap : ℝ) (hcap : ∀ u, colSum X u ≤ cap) (i : Fin m) :
    rowLocalizedDeficitTwoLoad X i ≤ rowCollisionLoad X i*
      ((32/27)*cap+(256/81)*rowCollisionIntensity X) := by
  have h := add_le_add (rowLocalizedTripletonLoad_le X hX hs hd cap hcap i)
    (rowLocalizedTwoDoubletonsLoad_le X hX hs hd i)
  apply h.trans_eq
  ring

/-- The coarser column-cap form of the localized deficit-two estimate. -/
theorem rowLocalizedDeficitTwoLoad_le_columnCap {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8)
    (cap : ℝ) (hcap : ∀ u, colSum X u ≤ cap) (i : Fin m) :
    rowLocalizedDeficitTwoLoad X i ≤ cap^2*((32/27)+(128/81)*(m:ℝ)) := by
  have hdcap (h : Fin m) := rowCollisionLoad_le_column_cap X hX hs hcap h
  have hd0 (h : Fin m) : 0 ≤ rowCollisionLoad X h :=
    Finset.sum_nonneg (fun j _ => rowCollisionProbability_nonneg X hX _ _)
  have hcap0 : 0 ≤ cap := (hd0 i).trans (hdcap i)
  have hD : rowCollisionIntensity X ≤ ((m:ℝ)/2)*cap := by
    unfold rowCollisionIntensity
    have hsum : (∑ h, rowCollisionLoad X h) ≤ (m:ℝ)*cap := by
      simpa using Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hdcap h)
    nlinarith
  have hD0 : 0 ≤ rowCollisionIntensity X :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun h _ => hd0 h))
  have hb : (32/27)*cap+(256/81)*rowCollisionIntensity X ≤
      (32/27)*cap+(256/81)*(((m:ℝ)/2)*cap) := by linarith
  have hb0 : 0 ≤ (32/27)*cap+(256/81)*rowCollisionIntensity X := by linarith
  have hmul := mul_le_mul (hdcap i) hb hb0 hcap0
  apply (rowLocalizedDeficitTwoLoad_le X hX hs hd cap hcap i).trans
  apply hmul.trans_eq
  ring

end DittertRybin
