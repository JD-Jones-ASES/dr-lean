import DR.Endpoint.PermanentFaceStationarity
import DR.Square.Transport
import DR.Endpoint.PositiveMaximizersGeometry

/-! Compactness and an actual minimum on every nonempty prescribed
doubly stochastic face, including additional zero entries. -/

namespace DittertRybin
open scoped BigOperators

def permanentFace {n : ℕ} (allowed : Fin n → Fin n → Prop) : Set (Board n n) :=
  {A | A ∈ doublyStochastic ℝ (Fin n) ∧ ∀ i j, ¬allowed i j → A i j = 0}

theorem isCompact_permanentFace {n : ℕ} (allowed : Fin n → Fin n → Prop) :
    IsCompact (permanentFace allowed) := by
  classical
  have hnonneg : IsClosed {A : Board n n | ∀ i j, 0 ≤ A i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
  have hrow : IsClosed {A : Board n n | ∀ i, rowSum A i = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (continuous_rowSum i) continuous_const
  have hcol : IsClosed {A : Board n n | ∀ j, colSum A j = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq (continuous_colSum j) continuous_const
  have hzero : IsClosed {A : Board n n | ∀ i j, ¬allowed i j → A i j = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  have hclosed : IsClosed (permanentFace allowed) := by
    have heq : permanentFace allowed =
        ({A : Board n n | ∀ i j, 0 ≤ A i j} ∩
          ({A | ∀ i, rowSum A i = 1} ∩ {A | ∀ j, colSum A j = 1})) ∩
        {A | ∀ i j, ¬allowed i j → A i j = 0} := by
      ext A
      simp [permanentFace, mem_doublyStochastic_iff_sum, rowSum, colSum]
    rw [heq]
    exact (hnonneg.inter (hrow.inter hcol)).inter hzero
  let box : Set (Board n n) := {A | ∀ i j, A i j ∈ Set.Icc 0 1}
  have hbox : IsCompact box :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset hclosed
  intro A hA i j
  refine ⟨nonneg_of_mem_doublyStochastic hA.1, ?_⟩
  calc
    A i j ≤ ∑ k, A i k := Finset.single_le_sum
      (f := fun k => A i k) (fun k _ => nonneg_of_mem_doublyStochastic hA.1)
      (Finset.mem_univ j)
    _ = 1 := sum_row_of_mem_doublyStochastic hA.1 i

theorem exists_permanentFaceMinimum {n : ℕ} {allowed : Fin n → Fin n → Prop}
    (hne : (permanentFace allowed).Nonempty) :
    ∃ A, PermanentFaceMinimum allowed A := by
  have hc : Continuous (fun A : Board n n => A.permanent) := by
    unfold Matrix.permanent
    fun_prop
  obtain ⟨A,hA,hmin⟩ := (isCompact_permanentFace allowed).exists_isMinOn hne hc.continuousOn
  exact ⟨A,hA.1,hA.2,fun B hB hz => hmin ⟨hB,hz⟩⟩

def LeastNormPermanentFaceMinimum {n : ℕ}
    (allowed : Fin n → Fin n → Prop) (A : Board n n) : Prop :=
  PermanentFaceMinimum allowed A ∧ ∀ B, PermanentFaceMinimum allowed B →
    orderThreeSquareSum A ≤ orderThreeSquareSum B

theorem exists_leastNormPermanentFaceMinimum {n : ℕ}
    {allowed : Fin n → Fin n → Prop} (hne : (permanentFace allowed).Nonempty) :
    ∃ A, LeastNormPermanentFaceMinimum allowed A := by
  obtain ⟨A₀,hA₀⟩ := exists_permanentFaceMinimum hne
  have hc : Continuous (fun A : Board n n => A.permanent) := by
    unfold Matrix.permanent
    fun_prop
  have hcompact : IsCompact {A : Board n n | A ∈ permanentFace allowed ∧
      A.permanent = A₀.permanent} :=
    (isCompact_permanentFace allowed).inter_right (isClosed_eq hc continuous_const)
  have henergy : Continuous (fun A : Board n n => orderThreeSquareSum A) := by
    unfold orderThreeSquareSum
    fun_prop
  obtain ⟨A,hA,hmin⟩ := hcompact.exists_isMinOn ⟨A₀,⟨hA₀.1,hA₀.2.1⟩,rfl⟩
    henergy.continuousOn
  have hAmin : PermanentFaceMinimum allowed A :=
    ⟨hA.1.1,hA.1.2,fun B hB hz => hA.2.trans_le (hA₀.2.2 B hB hz)⟩
  refine ⟨A,hAmin,fun B hB => hmin ⟨⟨hB.1,hB.2.1⟩,?_⟩⟩
  exact le_antisymm (hB.2.2 A₀ hA₀.1 hA₀.2.1) (hA₀.2.2 B hB.1 hB.2.1)

theorem PermanentFaceMinimum.transpose {n : ℕ}
    {allowed : Fin n → Fin n → Prop} {A : Board n n}
    (hA : PermanentFaceMinimum allowed A) :
    PermanentFaceMinimum (fun i j => allowed j i) A.transpose := by
  refine ⟨transpose_mem_doublyStochastic_iff.mpr hA.1, fun i j h => hA.2.1 j i h, ?_⟩
  intro B hB hz
  have h := hA.2.2 B.transpose (transpose_mem_doublyStochastic_iff.mpr hB)
    (fun i j h => hz j i h)
  simpa only [Matrix.permanent_transpose] using h

theorem LeastNormPermanentFaceMinimum.transpose {n : ℕ}
    {allowed : Fin n → Fin n → Prop} {A : Board n n}
    (hA : LeastNormPermanentFaceMinimum allowed A) :
    LeastNormPermanentFaceMinimum (fun i j => allowed j i) A.transpose := by
  refine ⟨hA.1.transpose, ?_⟩
  intro B hB
  have h := hA.2 B.transpose hB.transpose
  simpa only [orderThreeSquareSum_transpose] using h

end DittertRybin
