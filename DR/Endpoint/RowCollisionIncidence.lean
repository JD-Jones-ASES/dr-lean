import DR.Endpoint.RowDeletionQuadratic

/-! Actual collision-participation indicators. These definitions describe
events of the sampled assignment itself; no chosen labeling of its classes
is involved. -/

namespace DittertRybin
open scoped BigOperators
open Certificates

def RowCollisionParticipant {m n : ℕ} (z : Fin m → Fin n) (i : Fin m) : Prop :=
  ∃ j, i≠j ∧ z i=z j

def HasRowDoubletonPattern {m n : ℕ} (z : Fin m → Fin n) : Prop :=
  ∃ V : Finset (Fin m), V.card=2 ∧ RowClassPattern V z

def HasRowDeficitTwoPattern {m n : ℕ} (z : Fin m → Fin n) : Prop :=
  (∃ V : Finset (Fin m), V.card=3 ∧ RowClassPattern V z) ∨
  ∃ V W : Finset (Fin m), V.card=2 ∧ W.card=2 ∧ Disjoint V W ∧ RowTwoClassPattern V W z

noncomputable def rowDoubletonIncidence {m n : ℕ} (z : Fin m → Fin n) (i : Fin m) : ℝ := by
  classical
  exact if HasRowDoubletonPattern z ∧ RowCollisionParticipant z i then 1 else 0

noncomputable def rowDeficitTwoIncidence {m n : ℕ} (z : Fin m → Fin n) (i : Fin m) : ℝ := by
  classical
  exact if HasRowDeficitTwoPattern z ∧ RowCollisionParticipant z i then 1 else 0

theorem exists_other_of_card_gt_one {m : ℕ} (V : Finset (Fin m)) (hV : 1<V.card) (i : Fin m) :
    ∃ j∈V, i≠j := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hV
  by_cases hia : i=a
  · subst i
    exact ⟨b,hb,hab⟩
  · exact ⟨a,ha,hia⟩

/-- Every nontrivial class of an exact one-class assignment lies in its
prescribed class. This also excludes a second collision class. -/
theorem RowClassPattern.class_subset {m n : ℕ} {V U : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hU : 1<U.card) (hclass : RowClassEvent U z) : U⊆V := by
  intro i hi
  obtain ⟨j,hj,hij⟩ := exists_other_of_card_gt_one U hU i
  rcases (hz.eq_iff i j).mp (hclass i hi j hj) with he | hmem
  · exact (hij he).elim
  · exact hmem.1

theorem RowClassPattern.unique_class {m n : ℕ} {V U : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : 1<V.card)
    (hu : RowClassPattern U z) (hU : 1<U.card) : V=U :=
  Finset.Subset.antisymm (hu.class_subset hV hz.1) (hz.class_subset hU hu.1)

theorem RowClassPattern.participant_iff {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : 1<V.card) (i : Fin m) :
    RowCollisionParticipant z i ↔ i∈V := by
  constructor
  · rintro ⟨j,hij,he⟩
    rcases (hz.eq_iff i j).mp he with he | hmem
    · exact (hij he).elim
    · exact hmem.1
  · intro hi
    obtain ⟨j,hj,hij⟩ := exists_other_of_card_gt_one V hV i
    exact ⟨j,hij,hz.1 i hi j hj⟩

theorem RowTwoClassPattern.participant_iff {m n : ℕ} {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (hV : 1<V.card) (hW : 1<W.card) (i : Fin m) :
    RowCollisionParticipant z i ↔ i∈V∪W := by
  constructor
  · rintro ⟨j,hij,he⟩
    rcases (hz.eq_iff i j).mp he with he | hmem | hmem
    · exact (hij he).elim
    · exact Finset.mem_union_left _ hmem.1
    · exact Finset.mem_union_right _ hmem.1
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j,hj,hij⟩ := exists_other_of_card_gt_one V hV i
      exact ⟨j,hij,hz.1.1 i hi j hj⟩
    · obtain ⟨j,hj,hij⟩ := exists_other_of_card_gt_one W hW i
      exact ⟨j,hij,hz.1.2 i hi j hj⟩

theorem RowClassPattern.not_two_pairs {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card≤3) :
    ¬∃ U W : Finset (Fin m), U.card=2 ∧ W.card=2 ∧ Disjoint U W ∧ RowTwoClassPattern U W z := by
  rintro ⟨U,W,hU,hW,hdisj,hu⟩
  have hsU : U⊆V := hz.class_subset (by omega) hu.1.1
  have hsW : W⊆V := hz.class_subset (by omega) hu.1.2
  have hc := Finset.card_le_card (Finset.union_subset hsU hsW)
  rw [Finset.card_union_of_disjoint hdisj,hU,hW] at hc
  omega

theorem rowDoubleton_not_deficitTwo {m n : ℕ} {z : Fin m → Fin n}
    (h : HasRowDoubletonPattern z) : ¬HasRowDeficitTwoPattern z := by
  obtain ⟨V,hV,hz⟩ := h
  rintro (⟨U,hU,hu⟩ | htwo)
  · have he := hz.unique_class (by omega) hu (by omega)
    have hc := congrArg Finset.card he
    omega
  · exact hz.not_two_pairs (by omega) htwo

theorem rowDoubletonIncidence_of_pair {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=2) (i : Fin m) :
    rowDoubletonIncidence z i=rowClassIncidence V i := by
  classical
  have h : HasRowDoubletonPattern z := ⟨V,hV,hz⟩
  simp only [rowDoubletonIncidence,h,true_and,hz.participant_iff (by omega),rowClassIncidence]

theorem rowDeficitTwoIncidence_of_triple {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=3) (i : Fin m) :
    rowDeficitTwoIncidence z i=rowClassIncidence V i := by
  classical
  have h : HasRowDeficitTwoPattern z := Or.inl ⟨V,hV,hz⟩
  simp only [rowDeficitTwoIncidence,h,true_and,hz.participant_iff (by omega),rowClassIncidence]

theorem rowDeficitTwoIncidence_of_two_pairs {m n : ℕ} {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (hV : V.card=2) (hW : W.card=2)
    (hdisj : Disjoint V W) (i : Fin m) :
    rowDeficitTwoIncidence z i=rowClassIncidence (V∪W) i := by
  classical
  have h : HasRowDeficitTwoPattern z := Or.inr ⟨V,W,hV,hW,hdisj,hz⟩
  simp only [rowDeficitTwoIncidence,h,true_and,hz.participant_iff (by omega) (by omega),rowClassIncidence]

theorem rowCollisionParticipant_not_injective {m n : ℕ} {z : Fin m → Fin n}
    (hz : Function.Injective z) (i : Fin m) : ¬RowCollisionParticipant z i := by
  rintro ⟨j,hij,he⟩
  exact hij (hz he)

/-- The complete lower bound for each actual assignment, before taking
expectations. The class indicators count participation once, never edges. -/
theorem rowDeletion_pointwise_lower {m n : ℕ} (z : Fin m → Fin n) (x : Fin m → ℝ) :
    (if Function.Injective z then (∑ i,x i^2)-(∑ i,x i)^2 else 0)+
      (∑ i,rowDoubletonIncidence z i*x i^2)-
      2*(∑ i,x i)*(∑ i,rowDoubletonIncidence z i*x i)-
      2*(∑ i,rowDeficitTwoIncidence z i*x i^2) ≤
        -quadraticValue (rowDeletionMatrix z) x := by
  classical
  by_cases hinj : Function.Injective z
  · have hu (i : Fin m) : rowDoubletonIncidence z i=0 := by
      simp [rowDoubletonIncidence,rowCollisionParticipant_not_injective hinj i]
    have hv (i : Fin m) : rowDeficitTwoIncidence z i=0 := by
      simp [rowDeficitTwoIncidence,rowCollisionParticipant_not_injective hinj i]
    simp [hinj,hu,hv,neg_deletion_quadratic_of_injective hinj]
  · by_cases hpair : HasRowDoubletonPattern z
    · obtain ⟨V,hV,hz⟩ := hpair
      have hv (i : Fin m) : rowDeficitTwoIncidence z i=0 := by
        simp [rowDeficitTwoIncidence,rowDoubleton_not_deficitTwo ⟨V,hV,hz⟩]
      simp only [if_neg hinj,rowDoubletonIncidence_of_pair hz hV,hv,zero_mul,
        Finset.sum_const_zero,mul_zero,sub_zero,zero_add]
      exact hz.neg_deletion_quadratic_pair_lower hV x
    · have hu (i : Fin m) : rowDoubletonIncidence z i=0 := by
        simp [rowDoubletonIncidence,hpair]
      by_cases htwo : HasRowDeficitTwoPattern z
      · rcases htwo with ⟨V,hV,hz⟩ | ⟨V,W,hV,hW,hdisj,hz⟩
        · simp only [if_neg hinj,hu,rowDeficitTwoIncidence_of_triple hz hV,zero_mul,
            Finset.sum_const_zero,mul_zero,sub_zero,zero_add,zero_sub]
          simpa only [neg_mul] using hz.neg_deletion_quadratic_triple hV x
        · simp only [if_neg hinj,hu,rowDeficitTwoIncidence_of_two_pairs hz hV hW hdisj,
            zero_mul,Finset.sum_const_zero,mul_zero,sub_zero,zero_add,zero_sub]
          simpa only [neg_mul] using hz.neg_deletion_quadratic_two_pairs hV hW hdisj x
      · have hv (i : Fin m) : rowDeficitTwoIncidence z i=0 := by
          simp [rowDeficitTwoIncidence,htwo]
        have hzero : rowDeletionMatrix z=0 := by
          rcases rowDeletionMatrix_zero_or_pattern z with hzero | hi | hp | ht | ht
          · exact hzero
          · exact (hinj hi).elim
          · exact (hpair hp).elim
          · exact (htwo (Or.inl ht)).elim
          · exact (htwo (Or.inr ht)).elim
        simp [hinj,hu,hv,hzero,quadraticValue]

end DittertRybin
