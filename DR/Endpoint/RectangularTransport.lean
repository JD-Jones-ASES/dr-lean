import DR.Endpoint.RectangularTransportCuts

/-! Actual balanced rectangular transport dominated by arbitrary nonnegative
real capacities. Sufficiency reuses square transport through saturated dummy
rows; necessity retains the complementary cut, including boundary supports. -/
namespace DittertRybin
open scoped BigOperators

/-- A balanced rectangular matrix below the given capacities. -/
def IsRectangularTransport {m n : ℕ} (P B : Board m n) : Prop :=
  (∀ i j, 0 ≤ B i j) ∧ (∀ i j, B i j ≤ P i j) ∧
    (∀ i, rowSum B i = 1/(m : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ))

/-- Every dummy row of a feasible square transport saturates every capacity. -/
theorem rectangular_transport_dummy_saturated {m n : ℕ} (hmn : m ≤ n)
    (hm : 0 < m) (hn : 0 < n) (C : Board n n)
    (A : Board m n)
    (hC : IsTransport (rectangularCapacityPadding hmn A) (1/(m : ℝ)) C)
    (i : Fin (n-m)) (j : Fin n) :
    C (rectangularPaddingRowEquiv hmn (.inr i)) j = 1/((m : ℝ)*n) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let r := rectangularPaddingRowEquiv hmn (.inr i)
  have hrow : (∑ j, C r j) = 1/(m : ℝ) := hC.2.2.1 r
  have hcap (j : Fin n) : C r j ≤ 1/((m : ℝ)*n) := by
    simpa only [r, rectangularCapacityPadding_dummy] using hC.2.1 r j
  have hsum : (∑ _j : Fin n, 1/((m : ℝ)*n)) = 1/(m : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hz : (∑ j, (1/((m : ℝ)*n) - C r j)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, hrow, sub_self]
  have heach := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sub_nonneg.mpr (hcap j))).mp hz
  exact (sub_eq_zero.mp (heach j (Finset.mem_univ j))).symm

/-- The ordered-dimension case uses the already proved square cut theorem. -/
theorem exists_rectangularTransport_of_cuts_of_le {m n : ℕ} (hmn : m ≤ n)
    (hm : 0 < m) (hn : 0 < n) (P : Board m n)
    (hP : ∀ i j, 0 ≤ P i j) (hcuts : RectangularTransportCuts P) :
    ∃ B, IsRectangularTransport P B := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨C,hC⟩ := (transport_iff_cuts (rectangularCapacityPadding_nonneg hmn P hP)
    (by positivity : (0 : ℝ) ≤ 1/(m : ℝ))).mpr
      (rectangularCapacityPadding_transportCuts hmn hm hn P hcuts)
  let B : Board m n := fun i j => C (Fin.castLE hmn i) j
  have hdummy (i : Fin (n-m)) (j : Fin n) :
      C (rectangularPaddingRowEquiv hmn (.inr i)) j = 1/((m : ℝ)*n) :=
    rectangular_transport_dummy_saturated hmn hm hn C P hC i j
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact hC.1 _ _
  · intro i j
    simpa only [B, rectangularCapacityPadding_original hmn hm] using hC.2.1 (Fin.castLE hmn i) j
  · intro i
    exact hC.2.2.1 (Fin.castLE hmn i)
  · intro j
    have hsplit : colSum C j = colSum B j + ((n-m : ℕ) : ℝ)/((m : ℝ)*n) := by
      unfold colSum
      rw [← Equiv.sum_comp (rectangularPaddingRowEquiv hmn) (fun i => C i j),
        Fintype.sum_sum_type]
      simp only [rectangularPaddingRowEquiv_inl, hdummy, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, B]
      ring
    have hcol := hC.2.2.2 j
    rw [hsplit, Nat.cast_sub hmn] at hcol
    have hid : 1/(m : ℝ) - ((n : ℝ)-m)/((m : ℝ)*n) = 1/(n : ℝ) := by
      field_simp
      ring
    linarith

/-- Transposition exchanges the two rectangular cut demands exactly. -/
theorem RectangularTransportCuts.transpose {m n : ℕ} {P : Board m n}
    (h : RectangularTransportCuts P) : RectangularTransportCuts P.transpose := by
  intro I J
  have ht : cutMass P.transpose I J = cutMass P J I := by
    exact Finset.sum_comm
  rw [ht]
  simpa only [add_comm] using h J I

/-- Exact finite real-capacity transport, without an ordering of the dimensions. -/
theorem exists_rectangularTransport_of_cuts {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Board m n) (hP : ∀ i j, 0 ≤ P i j) (hcuts : RectangularTransportCuts P) :
    ∃ B, IsRectangularTransport P B := by
  rcases le_total m n with hmn | hnm
  · exact exists_rectangularTransport_of_cuts_of_le hmn hm hn P hP hcuts
  · obtain ⟨B,hB⟩ := exists_rectangularTransport_of_cuts_of_le hnm hn hm P.transpose
      (fun i j => hP j i) hcuts.transpose
    refine ⟨B.transpose, ?_, ?_, ?_, ?_⟩
    · intro i j
      exact hB.1 j i
    · intro i j
      exact hB.2.1 j i
    · intro i
      exact hB.2.2.2 i
    · intro j
      exact hB.2.2.1 j

/-- A balanced dominated matrix supplies every cut, not only positive cuts. -/
theorem IsRectangularTransport.cuts {m n : ℕ} {P B : Board m n}
    (h : IsRectangularTransport P B) (hn : 0 < n) : RectangularTransportCuts P := by
  intro I J
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hr := cutMass_add_compl_cols B I J
  have hc := cutMass_add_compl_rows B I Jᶜ
  simp only [h.2.2.1, h.2.2.2, Finset.sum_const, nsmul_eq_mul] at hr hc
  have hcard : (Jᶜ.card : ℝ) = n-J.card := by
    have hs : (J.card : ℝ) + Jᶜ.card = n := by
      exact_mod_cast (show J.card + Jᶜ.card = n by simp)
    linarith
  rw [hcard] at hc
  have hid : ((n : ℝ)-J.card)*(1/(n : ℝ)) = 1-(J.card : ℝ)/n := by
    field_simp
  have hcomp := cutMass_nonneg h.1 Iᶜ Jᶜ
  have hmono := cutMass_mono h.2.1 I J
  rw [hid] at hc
  simp only [div_eq_mul_inv] at hr hc ⊢
  linarith

/-- Necessary and sufficient rectangular cut criterion. -/
theorem rectangularTransport_iff_cuts {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Board m n) (hP : ∀ i j, 0 ≤ P i j) :
    (∃ B, IsRectangularTransport P B) ↔ RectangularTransportCuts P := by
  constructor
  · rintro ⟨B,hB⟩
    exact hB.cuts hn
  · exact exists_rectangularTransport_of_cuts hm hn P hP

/-- The resulting balanced transport is a probability board. -/
theorem IsRectangularTransport.isProbability {m n : ℕ} {P B : Board m n}
    (h : IsRectangularTransport P B) (hm : 0 < m) : IsProbability B := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  refine ⟨h.1, ?_⟩
  simp [totalMass, h.2.2.1, hm0]

/-- A zero capacity remains a zero in every dominated balanced transport. -/
theorem IsRectangularTransport.zero_of_capacity_zero {m n : ℕ} {P B : Board m n}
    (h : IsRectangularTransport P B) (i : Fin m) (j : Fin n) (hz : P i j = 0) :
    B i j = 0 := by
  apply le_antisymm
  · simpa only [hz] using h.2.1 i j
  · exact h.1 i j

/-- Boundary support is preserved by the constructed dominated matrix. -/
theorem IsRectangularTransport.hasZero {m n : ℕ} {P B : Board m n}
    (h : IsRectangularTransport P B) (hz : ∃ i j, P i j = 0) : ∃ i j, B i j = 0 := by
  obtain ⟨i,j,hz⟩ := hz
  exact ⟨i,j,h.zero_of_capacity_zero i j hz⟩

/-- Explicit matrix interface for the endpoint balanced-domination argument. -/
theorem exists_balanced_dominated_of_rectangular_cuts {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (P : Board m n) (hP : ∀ i j, 0 ≤ P i j)
    (hcuts : ∀ (I : Finset (Fin m)) (J : Finset (Fin n)),
      (I.card : ℝ)/m + (J.card : ℝ)/n - 1 ≤ cutMass P I J) :
    ∃ B : Board m n, (∀ i j, 0 ≤ B i j) ∧
      (∀ i, rowSum B i = 1/(m : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ)) ∧
        ∀ i j, B i j ≤ P i j := by
  obtain ⟨B,hB⟩ := exists_rectangularTransport_of_cuts hm hn P hP hcuts
  exact ⟨B,hB.1,hB.2.2.1,hB.2.2.2,hB.2.1⟩

end DittertRybin
