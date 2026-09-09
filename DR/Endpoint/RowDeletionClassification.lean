import DR.Endpoint.RowDeletionPatterns

/-! Every assignment that can be repaired by deleting two distinct rows
has no collision, exactly one doubleton, one tripleton, or two disjoint
doubletons. This is a finite equality-class argument, with no probability
or optimizer hypothesis. -/

namespace DittertRybin

/-- The actual row fiber of a sampled column. -/
def rowColumnFiber {m n : ℕ} (z : Fin m → Fin n) (u : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun i => z i=u)

theorem rowColumnFiber_class {m n : ℕ} (z : Fin m → Fin n) (u : Fin n) :
    RowClassEvent (rowColumnFiber z u) z := by
  intro i hi j hj
  exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm

theorem rowColumnFiber_disjoint {m n : ℕ} (z : Fin m → Fin n) (u v : Fin n) (huv : u ≠ v) :
    Disjoint (rowColumnFiber z u) (rowColumnFiber z v) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact huv ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem rowColumnFiber_outside_card_le_one {m n : ℕ} {z : Fin m → Fin n}
    (S : Finset (Fin m)) (hdel : RowsDistinctOutside S z) (u : Fin n) :
    (rowColumnFiber z u \ S).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := Finset.mem_sdiff.mp hi
  have hj' := Finset.mem_sdiff.mp hj
  exact hdel i hi'.2 j hj'.2 ((rowColumnFiber_class z u) i hi'.1 j hj'.1)

/-- All collisions in a repairable assignment lie in the fibers of the
two deleted rows. Other rows are already distinct. -/
theorem two_row_fibers_pattern {m n : ℕ} {z : Fin m → Fin n} (a b : Fin m)
    (hdel : RowsDistinctOutside {a,b} z) :
    RowTwoClassPattern (rowColumnFiber z (z a)) (rowColumnFiber z (z b)) z := by
  classical
  refine ⟨⟨rowColumnFiber_class z (z a),rowColumnFiber_class z (z b)⟩,?_⟩
  intro e he hE
  have heN := (Finset.mem_sdiff.mp he).2
  have hna : ¬(z e.val.1=z a ∧ z e.val.2=z a) := by
    intro h
    apply heN
    apply Finset.mem_union_left
    simp only [rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and,rowColumnFiber]
    exact h
  have hnb : ¬(z e.val.1=z b ∧ z e.val.2=z b) := by
    intro h
    apply heN
    apply Finset.mem_union_right
    simp only [rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and,rowColumnFiber]
    exact h
  have heq : z e.val.1=z e.val.2 := hE
  have h1 : e.val.1 ∉ ({a,b} : Finset (Fin m)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    constructor
    · intro h; exact hna ⟨congrArg z h,heq.symm.trans (congrArg z h)⟩
    · intro h; exact hnb ⟨congrArg z h,heq.symm.trans (congrArg z h)⟩
  have h2 : e.val.2 ∉ ({a,b} : Finset (Fin m)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    constructor
    · intro h; exact hna ⟨heq.trans (congrArg z h),congrArg z h⟩
    · intro h; exact hnb ⟨heq.trans (congrArg z h),congrArg z h⟩
  exact (ne_of_lt e.property) (hdel _ h1 _ h2 heq)

/-- A singleton prescribed class contributes no nontrivial collision. -/
theorem RowTwoClassPattern.drop_singleton_right {m n : ℕ} {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) (hW : W.card ≤ 1) : RowClassPattern V z := by
  classical
  refine ⟨hz.1.1,?_⟩
  intro e he hE
  rcases (hz.eq_iff e.val.1 e.val.2).mp hE with heq | hV | hW'
  · exact (ne_of_lt e.property) heq
  · apply (Finset.mem_sdiff.mp he).2
    simpa only [rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hV
  · exact (ne_of_lt e.property) (Finset.card_le_one.mp hW _ hW'.1 _ hW'.2)

theorem RowTwoClassPattern.swap {m n : ℕ} {V W : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowTwoClassPattern V W z) : RowTwoClassPattern W V z := by
  simpa only [RowTwoClassPattern,Finset.union_comm,and_comm] using hz

theorem RowClassPattern.injective_of_card_le_one {m n : ℕ} {V : Finset (Fin m)} {z : Fin m → Fin n}
    (hz : RowClassPattern V z) (hV : V.card ≤ 1) : Function.Injective z := by
  intro i j he
  rcases (hz.eq_iff i j).mp he with hij | hmem
  · exact hij
  · exact Finset.card_le_one.mp hV _ hmem.1 _ hmem.2

/-- Complete classification of every assignment admitting a successful
two-row deletion. Cardinalities refer to the actual equality classes. -/
theorem classify_two_row_deletion {m n : ℕ} (z : Fin m → Fin n) (a b : Fin m)
    (hab : a ≠ b) (hdel : RowsDistinctOutside {a,b} z) :
    Function.Injective z ∨
      (∃ V : Finset (Fin m), V.card=2 ∧ RowClassPattern V z) ∨
      (∃ V : Finset (Fin m), V.card=3 ∧ RowClassPattern V z) ∨
      ∃ V W : Finset (Fin m), V.card=2 ∧ W.card=2 ∧ Disjoint V W ∧ RowTwoClassPattern V W z := by
  classical
  let V := rowColumnFiber z (z a)
  let W := rowColumnFiber z (z b)
  have ha : a ∈ V := by simp [V,rowColumnFiber]
  have hb : b ∈ W := by simp [W,rowColumnFiber]
  have hvpos : 1 ≤ V.card := Finset.one_le_card.mpr ⟨a,ha⟩
  have hwpos : 1 ≤ W.card := Finset.one_le_card.mpr ⟨b,hb⟩
  have hVout := rowColumnFiber_outside_card_le_one {a,b} hdel (z a)
  have hWout := rowColumnFiber_outside_card_le_one {a,b} hdel (z b)
  change (V \ {a,b}).card ≤ 1 at hVout
  change (W \ {a,b}).card ≤ 1 at hWout
  have hp : RowTwoClassPattern V W z := two_row_fibers_pattern a b hdel
  by_cases heq : z a=z b
  · have hVW : V=W := by simp only [V,W,heq]
    have hbV : b ∈ V := hVW ▸ hb
    have hsub : ({a,b} : Finset (Fin m)) ⊆ V := by
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> assumption
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    have hpair : ({a,b} : Finset (Fin m)).card=2 := by simp [hab]
    rw [hpair] at hc
    have hclass : RowClassPattern V z := by
      rw [← hVW] at hp
      simpa only [RowTwoClassPattern,RowClassPattern,and_self,Finset.union_self] using hp
    have hcases : V.card=2 ∨ V.card=3 := by omega
    rcases hcases with hc | hc
    · exact Or.inr (Or.inl ⟨V,hc,hclass⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨V,hc,hclass⟩))
  · have hdisj : Disjoint V W := rowColumnFiber_disjoint z _ _ heq
    have hbV : b ∉ V := fun h => Finset.disjoint_left.mp hdisj h hb
    have haW : a ∉ W := fun h => Finset.disjoint_left.mp hdisj ha h
    have hcV := Finset.card_sdiff_add_card_inter V ({a,b} : Finset (Fin m))
    have hcW := Finset.card_sdiff_add_card_inter W ({a,b} : Finset (Fin m))
    have hintV : V ∩ {a,b}={a} := by
      ext i
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨hi,rfl | rfl⟩
        · rfl
        · exact (hbV hi).elim
      · rintro rfl; exact ⟨ha,Or.inl rfl⟩
    have hintW : W ∩ {a,b}={b} := by
      ext i
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨hi,rfl | rfl⟩
        · exact (haW hi).elim
        · rfl
      · rintro rfl; exact ⟨hb,Or.inr rfl⟩
    rw [hintV,Finset.card_singleton] at hcV
    rw [hintW,Finset.card_singleton] at hcW
    have hVc : V.card=1 ∨ V.card=2 := by omega
    have hWc : W.card=1 ∨ W.card=2 := by omega
    rcases hVc with hVc | hVc <;> rcases hWc with hWc | hWc
    · exact Or.inl ((hp.drop_singleton_right hWc.le).injective_of_card_le_one hVc.le)
    · exact Or.inr (Or.inl ⟨W,hWc,hp.swap.drop_singleton_right hVc.le⟩)
    · exact Or.inr (Or.inl ⟨V,hVc,hp.drop_singleton_right hWc.le⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨V,W,hVc,hWc,hdisj,hp⟩))

/-- The exhaustive form used under expectation. Assignments outside the four
listed patterns have the zero deletion matrix, including several larger
collision classes and any number of distinct sampled columns. -/
theorem rowDeletionMatrix_zero_or_pattern {m n : ℕ} (z : Fin m → Fin n) :
    rowDeletionMatrix z=0 ∨ Function.Injective z ∨
      (∃ V : Finset (Fin m), V.card=2 ∧ RowClassPattern V z) ∨
      (∃ V : Finset (Fin m), V.card=3 ∧ RowClassPattern V z) ∨
      ∃ V W : Finset (Fin m), V.card=2 ∧ W.card=2 ∧ Disjoint V W ∧ RowTwoClassPattern V W z := by
  classical
  by_cases h : ∃ a b, a ≠ b ∧ RowsDistinctOutside {a,b} z
  · obtain ⟨a,b,hab,hdel⟩ := h
    exact Or.inr (classify_two_row_deletion z a b hab hdel)
  · left
    funext a b
    by_cases hab : a=b
    · subst b
      exact rowDeletionMatrix_self z a
    · have hdel : ¬RowsDistinctOutside {a,b} z := fun hdel => h ⟨a,b,hab,hdel⟩
      simp only [rowDeletionMatrix,if_neg hab,if_neg hdel,Matrix.zero_apply]

end DittertRybin
