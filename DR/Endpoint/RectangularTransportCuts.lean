import DR.Endpoint.RectangularPadding
import DR.Square.Transport

/-! Exact rectangular cuts reduce to the previously proved square transport
criterion by adjoining saturated dummy rows. No desired transport is assumed. -/
namespace DittertRybin
open scoped BigOperators

/-- Every rectangular capacity cut, including negative and zero demands. -/
def RectangularTransportCuts {m n : ℕ} (P : Board m n) : Prop :=
  ∀ (I : Finset (Fin m)) (J : Finset (Fin n)),
    (I.card : ℝ)/m + (J.card : ℝ)/n - 1 ≤ cutMass P I J

/-- Original indices selected by a cut of the padded square. -/
def rectangularOriginalCut {m n : ℕ} (hmn : m ≤ n) (I : Finset (Fin n)) :
    Finset (Fin m) := Finset.univ.filter fun i => Fin.castLE hmn i ∈ I

/-- Dummy indices selected by a cut of the padded square. -/
def rectangularDummyCut {m n : ℕ} (hmn : m ≤ n) (I : Finset (Fin n)) :
    Finset (Fin (n-m)) := Finset.univ.filter fun i =>
      rectangularPaddingRowEquiv hmn (.inr i) ∈ I

/-- Exact splitting of any finite row sum across original and dummy rows. -/
theorem rectangular_cut_sum_split {m n : ℕ} (hmn : m ≤ n)
    {R : Type*} [AddCommMonoid R] (f : Fin n → R) (I : Finset (Fin n)) :
    (∑ i ∈ I, f i) =
      (∑ i ∈ rectangularOriginalCut hmn I, f (Fin.castLE hmn i)) +
      ∑ i ∈ rectangularDummyCut hmn I, f (rectangularPaddingRowEquiv hmn (.inr i)) := by
  simpa [Fintype.sum_sum_type, rectangularOriginalCut, rectangularDummyCut,
    Finset.sum_filter] using
    (Equiv.sum_comp (rectangularPaddingRowEquiv hmn) (fun i => if i ∈ I then f i else 0)).symm

/-- The two selected row parts have exactly the original cut cardinality. -/
theorem rectangular_cut_card_split {m n : ℕ} (hmn : m ≤ n) (I : Finset (Fin n)) :
    I.card = (rectangularOriginalCut hmn I).card + (rectangularDummyCut hmn I).card := by
  simpa using rectangular_cut_sum_split hmn (fun _ => (1 : ℕ)) I

/-- Original capacities are unchanged; dummy cells have capacity1/(mn). -/
noncomputable def rectangularCapacityPadding {m n : ℕ} (hmn : m ≤ n)
    (P : Board m n) : Board n n := (1/(m : ℝ)) • rectangularPadding hmn P

@[simp] theorem rectangularCapacityPadding_original {m n : ℕ} (hmn : m ≤ n)
    (hm : 0 < m) (P : Board m n) (i : Fin m) (j : Fin n) :
    rectangularCapacityPadding hmn P (Fin.castLE hmn i) j = P i j := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp [rectangularCapacityPadding, hm0]

@[simp] theorem rectangularCapacityPadding_dummy {m n : ℕ} (hmn : m ≤ n)
    (P : Board m n) (i : Fin (n-m)) (j : Fin n) :
    rectangularCapacityPadding hmn P (rectangularPaddingRowEquiv hmn (.inr i)) j =
      1/((m : ℝ)*n) := by
  simp [rectangularCapacityPadding, mul_comm]

theorem rectangularCapacityPadding_nonneg {m n : ℕ} (hmn : m ≤ n)
    (P : Board m n) (hP : ∀ i j, 0 ≤ P i j) :
    ∀ i j, 0 ≤ rectangularCapacityPadding hmn P i j := by
  intro i j
  exact mul_nonneg (by positivity) (rectangularPadding_nonneg hmn P hP i j)

/-- Exact mass in an arbitrary cut of the padded capacity matrix. -/
theorem cutMass_rectangularCapacityPadding {m n : ℕ} (hmn : m ≤ n)
    (hm : 0 < m) (P : Board m n) (I J : Finset (Fin n)) :
    cutMass (rectangularCapacityPadding hmn P) I J =
      cutMass P (rectangularOriginalCut hmn I) J +
        ((rectangularDummyCut hmn I).card : ℝ) * J.card / ((m : ℝ)*n) := by
  unfold cutMass
  rw [rectangular_cut_sum_split hmn]
  simp only [rectangularCapacityPadding_original hmn hm, rectangularCapacityPadding_dummy,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- All square cuts follow from the rectangular cuts. The extra slack is
((n−m)−r)*(n−|J|)/(mn), where r is the selected dummy-row count. -/
theorem rectangularCapacityPadding_transportCuts {m n : ℕ} (hmn : m ≤ n)
    (hm : 0 < m) (hn : 0 < n) (P : Board m n) (hcuts : RectangularTransportCuts P) :
    TransportCuts (rectangularCapacityPadding hmn P) (1/(m : ℝ)) := by
  intro I J
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (I.card : ℝ) = (rectangularOriginalCut hmn I).card +
      (rectangularDummyCut hmn I).card := by
    exact_mod_cast rectangular_cut_card_split hmn I
  have hd : ((rectangularDummyCut hmn I).card : ℝ) ≤ (n : ℝ)-m := by
    have h := Finset.card_le_univ (s := rectangularDummyCut hmn I)
    have : (rectangularDummyCut hmn I).card ≤ n-m := by simpa using h
    exact_mod_cast this
  have hJ : (J.card : ℝ) ≤ n := by
    exact_mod_cast (show J.card ≤ n by simpa using Finset.card_le_univ (s := J))
  have hslack : 0 ≤ ((n : ℝ)-m-(rectangularDummyCut hmn I).card) *
      ((n : ℝ)-J.card) / ((m : ℝ)*n) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hmR hnR).le
  have hid :
      ((rectangularOriginalCut hmn I).card : ℝ)/m + (J.card : ℝ)/n - 1 +
        ((rectangularDummyCut hmn I).card : ℝ)*J.card/((m : ℝ)*n) -
          (1/(m : ℝ))*((I.card : ℝ)+J.card-n) =
      ((n : ℝ)-m-(rectangularDummyCut hmn I).card)*((n : ℝ)-J.card)/((m : ℝ)*n) := by
    rw [hcard]
    field_simp
    ring
  have hc := hcuts (rectangularOriginalCut hmn I) J
  rw [cutMass_rectangularCapacityPadding hmn hm]
  linarith

end DittertRybin
