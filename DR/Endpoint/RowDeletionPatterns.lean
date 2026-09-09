import DR.Endpoint.RowCollisionTwoClasses

/-! Literal deletion-of-two-rows matrices on actual assignments. Exact
one- and two-class patterns determine all row equality relations, so
deletion succeeds precisely when at most one row of each class remains. -/

namespace DittertRybin
open scoped BigOperators

/-- The remaining sampled columns are distinct after deleting S. -/
def RowsDistinctOutside {m n : ℕ} (S : Finset (Fin m)) (z : Fin m → Fin n) : Prop :=
  ∀ i, i ∉ S → ∀ j, j ∉ S → z i=z j → i=j

/-- The actual zero-diagonal two-row deletion matrix. -/
noncomputable def rowDeletionMatrix {m n : ℕ} (z : Fin m → Fin n) : Matrix (Fin m) (Fin m) ℝ := by
  classical
  exact fun a b => if a=b then 0 else if RowsDistinctOutside {a,b} z then 1 else 0

theorem rowDeletionMatrix_self {m n : ℕ} (z : Fin m → Fin n) (a : Fin m) :
    rowDeletionMatrix z a a=0 := by simp [rowDeletionMatrix]

theorem rowDeletionMatrix_symmetric {m n : ℕ} (z : Fin m → Fin n) :
    (rowDeletionMatrix z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  unfold rowDeletionMatrix
  rw [Finset.pair_comm a b]
  by_cases hab : a=b
  · subst b
    rfl
  · simp only [if_neg hab,if_neg (Ne.symm hab)]

/-- Every true collision edge must lie among the explicitly removed edges. -/
theorem rowCollision_mem_of_avoid {m n : ℕ} (z : Fin m → Fin n)
    (L : Finset (SampleIndexPair m))
    (havoid : ∀ e ∈ Finset.univ \ L, ¬RowCollisionEvent e z)
    (e : SampleIndexPair m) (he : RowCollisionEvent e z) : e ∈ L := by
  classical
  by_contra hn
  exact havoid e (by simp [hn]) he

/-- An exact one-class pattern determines the complete equality relation. -/
theorem RowClassPattern.eq_iff {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (i j : Fin m) :
    z i=z j ↔ i=j ∨ (i ∈ V ∧ j ∈ V) := by
  constructor
  · intro he
    by_cases hij : i=j
    · exact Or.inl hij
    · right
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · have h := rowCollision_mem_of_avoid z (rowClassEdges V) hz.2 ⟨(i,j),hlt⟩ he
        simpa only [rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and] using h
      · have h := rowCollision_mem_of_avoid z (rowClassEdges V) hz.2 ⟨(j,i),hlt⟩ he.symm
        have hm : j ∈ V ∧ i ∈ V := by
          simpa only [rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and] using h
        exact hm.symm
  · rintro (rfl | ⟨hi,hj⟩)
    · rfl
    · exact hz.1 i hi j hj

/-- An exact two-class pattern determines the complete equality relation,
including exclusion of cross-class and outside collisions. -/
theorem RowTwoClassPattern.eq_iff {m n : ℕ} {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (i j : Fin m) :
    z i=z j ↔ i=j ∨ (i ∈ V ∧ j ∈ V) ∨ (i ∈ W ∧ j ∈ W) := by
  constructor
  · intro he
    by_cases hij : i=j
    · exact Or.inl hij
    · right
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · have h := rowCollision_mem_of_avoid z (rowClassEdges V ∪ rowClassEdges W) hz.2 ⟨(i,j),hlt⟩ he
        simpa only [Finset.mem_union,rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and] using h
      · have h := rowCollision_mem_of_avoid z (rowClassEdges V ∪ rowClassEdges W) hz.2 ⟨(j,i),hlt⟩ he.symm
        have hm : (j ∈ V ∧ i ∈ V) ∨ (j ∈ W ∧ i ∈ W) := by
          simpa only [Finset.mem_union,rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and] using h
        exact hm.imp And.symm And.symm
  · rintro (rfl | ⟨hi,hj⟩ | ⟨hi,hj⟩)
    · rfl
    · exact hz.1.1 i hi j hj
    · exact hz.1.2 i hi j hj

/-- For a one-class pattern, distinctness after any row deletion is an
exact finite cardinality condition. -/
theorem RowClassPattern.distinctOutside_iff {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (S : Finset (Fin m)) :
    RowsDistinctOutside S z ↔ (V \ S).card ≤ 1 := by
  constructor
  · intro h
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := Finset.mem_sdiff.mp hi
    have hj' := Finset.mem_sdiff.mp hj
    exact h i hi'.2 j hj'.2 (hz.1 i hi'.1 j hj'.1)
  · intro h i hi j hj he
    rcases (hz.eq_iff i j).mp he with hij | ⟨hiV,hjV⟩
    · exact hij
    · exact Finset.card_le_one.mp h i (Finset.mem_sdiff.mpr ⟨hiV,hi⟩) j (Finset.mem_sdiff.mpr ⟨hjV,hj⟩)

/-- Each prescribed class must retain at most one row after deletion. -/
theorem RowTwoClassPattern.distinctOutside_iff {m n : ℕ} {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (S : Finset (Fin m)) :
    RowsDistinctOutside S z ↔ (V \ S).card ≤ 1 ∧ (W \ S).card ≤ 1 := by
  constructor
  · intro h
    constructor
    · apply Finset.card_le_one.mpr
      intro i hi j hj
      have hi' := Finset.mem_sdiff.mp hi
      have hj' := Finset.mem_sdiff.mp hj
      exact h i hi'.2 j hj'.2 (hz.1.1 i hi'.1 j hj'.1)
    · apply Finset.card_le_one.mpr
      intro i hi j hj
      have hi' := Finset.mem_sdiff.mp hi
      have hj' := Finset.mem_sdiff.mp hj
      exact h i hi'.2 j hj'.2 (hz.1.2 i hi'.1 j hj'.1)
  · rintro ⟨hV,hW⟩ i hi j hj he
    rcases (hz.eq_iff i j).mp he with hij | ⟨hiV,hjV⟩ | ⟨hiW,hjW⟩
    · exact hij
    · exact Finset.card_le_one.mp hV i (Finset.mem_sdiff.mpr ⟨hiV,hi⟩) j (Finset.mem_sdiff.mpr ⟨hjV,hj⟩)
    · exact Finset.card_le_one.mp hW i (Finset.mem_sdiff.mpr ⟨hiW,hi⟩) j (Finset.mem_sdiff.mpr ⟨hjW,hj⟩)

theorem rowDeletionMatrix_of_injective {m n : ℕ} {z : Fin m → Fin n}
    (hz : Function.Injective z) (a b : Fin m) :
    rowDeletionMatrix z a b = if a=b then 0 else 1 := by
  classical
  have h : RowsDistinctOutside {a,b} z := fun i _ j _ he => hz he
  simp [rowDeletionMatrix,h]

theorem RowClassPattern.deletionMatrix {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (a b : Fin m) :
    rowDeletionMatrix z a b = if a=b then 0 else if (V \ {a,b}).card ≤ 1 then 1 else 0 := by
  classical
  simp only [rowDeletionMatrix,hz.distinctOutside_iff]

theorem RowTwoClassPattern.deletionMatrix {m n : ℕ} {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (a b : Fin m) :
    rowDeletionMatrix z a b = if a=b then 0 else
      if (V \ {a,b}).card ≤ 1 ∧ (W \ {a,b}).card ≤ 1 then 1 else 0 := by
  classical
  simp only [rowDeletionMatrix,hz.distinctOutside_iff]

/-- Deleting two positions breaks a two-element class exactly when one is hit. -/
theorem card_pair_deletion_two_iff {m : ℕ} (V : Finset (Fin m)) (hV : V.card=2) (a b : Fin m) :
    (V \ {a,b}).card ≤ 1 ↔ a ∈ V ∨ b ∈ V := by
  classical
  by_cases ha : a ∈ V <;> by_cases hb : b ∈ V <;> by_cases hab : a=b <;>
    simp [Finset.card_sdiff,hV,ha,hb,hab]

/-- Deleting two distinct positions breaks a three-element class exactly
when both positions lie in the class. -/
theorem card_pair_deletion_three_iff {m : ℕ} (V : Finset (Fin m)) (hV : V.card=3)
    (a b : Fin m) (hab : a ≠ b) : (V \ {a,b}).card ≤ 1 ↔ a ∈ V ∧ b ∈ V := by
  classical
  by_cases ha : a ∈ V <;> by_cases hb : b ∈ V <;>
    simp [Finset.card_sdiff,hV,ha,hb,hab]

theorem RowClassPattern.deletionMatrix_pair {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=2) (a b : Fin m) :
    rowDeletionMatrix z a b = if a=b then 0 else if a ∈ V ∨ b ∈ V then 1 else 0 := by
  classical
  simp only [hz.deletionMatrix,card_pair_deletion_two_iff V hV]

theorem RowClassPattern.deletionMatrix_triple {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=3) (a b : Fin m) :
    rowDeletionMatrix z a b = if a=b then 0 else if a ∈ V ∧ b ∈ V then 1 else 0 := by
  classical
  rw [hz.deletionMatrix]
  by_cases hab : a=b
  · simp [hab]
  · simp only [if_neg hab,card_pair_deletion_three_iff V hV a b hab]

theorem RowTwoClassPattern.deletionMatrix_two_pairs {m n : ℕ} {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (hV : V.card=2) (hW : W.card=2)
    (hdisj : Disjoint V W) (a b : Fin m) :
    rowDeletionMatrix z a b = if a=b then 0 else
      if (a ∈ V ∧ b ∈ W) ∨ (a ∈ W ∧ b ∈ V) then 1 else 0 := by
  classical
  simp only [hz.deletionMatrix,card_pair_deletion_two_iff V hV,card_pair_deletion_two_iff W hW]
  have ha : ¬(a ∈ V ∧ a ∈ W) := fun h => Finset.disjoint_left.mp hdisj h.1 h.2
  have hb : ¬(b ∈ V ∧ b ∈ W) := fun h => Finset.disjoint_left.mp hdisj h.1 h.2
  have he : ((a ∈ V ∨ b ∈ V) ∧ (a ∈ W ∨ b ∈ W)) ↔
      ((a ∈ V ∧ b ∈ W) ∨ (a ∈ W ∧ b ∈ V)) := by tauto
  simp only [he]

/-- The literal zero-one incidence vector of a row set. -/
def rowClassIncidence {m : ℕ} (V : Finset (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ V then 1 else 0

/-- Exact single-doubleton matrix identity before dropping its positive
rank-one incidence term. -/
theorem RowClassPattern.neg_deletionMatrix_pair {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card=2) (a b : Fin m) :
    -rowDeletionMatrix z a b =
      (if a=b then rowClassIncidence V a else 0)-rowClassIncidence V a-rowClassIncidence V b+
        rowClassIncidence V a*rowClassIncidence V b := by
  classical
  rw [hz.deletionMatrix_pair hV]
  by_cases hab : a=b
  · subst b
    by_cases ha : a ∈ V <;> norm_num [rowClassIncidence,ha]
  · by_cases ha : a ∈ V <;> by_cases hb : b ∈ V <;> norm_num [rowClassIncidence,ha,hb,hab]

/-- A class of size at least four cannot be repaired by deleting two rows. -/
theorem RowClassPattern.deletionMatrix_zero_of_large {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : 4 ≤ V.card) (a b : Fin m) :
    rowDeletionMatrix z a b=0 := by
  classical
  have h := Finset.card_le_card_sdiff_add_card (s := V) (t := {a,b})
  have hp : ({a,b} : Finset (Fin m)).card ≤ 2 := by
    simpa using Finset.card_insert_le a ({b} : Finset (Fin m))
  have hn : ¬(V \ {a,b}).card ≤ 1 := by omega
  rw [hz.deletionMatrix]
  simp [hn]

end DittertRybin
