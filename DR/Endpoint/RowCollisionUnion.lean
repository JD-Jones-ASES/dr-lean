import DR.Endpoint.RowCollisions
import DR.Collision.Bonferroni

/-! The independent-row collision graph has one edge per increasing pair.
Its total event mass is the half-ordered intensity, and its union is exactly
the complement of the actual injection event. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem rowAssignmentEvent_eq_finiteMass {m n : ℕ} (X : Board m n)
    (E : Set (Fin m → Fin n)) :
    rowAssignmentEvent X E = FiniteEvents.mass Finset.univ (rowAssignmentMass X)
      (fun z => z ∈ E) := by
  classical
  unfold rowAssignmentEvent FiniteEvents.mass
  apply Finset.sum_congr rfl
  intro z hz
  by_cases he : z ∈ E <;> simp [FiniteEvents.indicator,he]

/-- A finite union bound for the actual independent row distributions. -/
theorem rowAssignmentEvent_union_bound {m n : ℕ} {ι : Type*}
    (X : Board m n) (hX : ∀ i j, 0 ≤ X i j)
    (I : Finset ι) (E : ι → (Fin m → Fin n) → Prop) :
    rowAssignmentEvent X {z | ∃ a ∈ I, E a z} ≤
      ∑ a ∈ I, rowAssignmentEvent X {z | E a z} := by
  simp_rw [rowAssignmentEvent_eq_finiteMass]
  exact FiniteEvents.union_bound Finset.univ I (rowAssignmentMass X) E
    (fun z _ => rowAssignmentMass_nonneg X hX z)

/-- The two orientations of every edge have exactly equal probability. -/
theorem rowCollisionIntensity_eq_sum_lt {m n : ℕ} (X : Board m n) :
    rowCollisionIntensity X = ∑ i, ∑ h, if i < h then rowCollisionProbability X i h else 0 := by
  classical
  have he (i : Fin m) : rowCollisionLoad X i =
      (∑ h, if i < h then rowCollisionProbability X i h else 0)+
        (∑ h, if h < i then rowCollisionProbability X i h else 0) := by
    have hr : rowCollisionLoad X i = ∑ h ∈ Finset.univ.erase i,
        ((if i < h then rowCollisionProbability X i h else 0)+
          (if h < i then rowCollisionProbability X i h else 0)) := by
      apply Finset.sum_congr rfl
      intro h hh
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hh) with hl | hl
      · simp [hl,not_lt_of_gt hl]
      · simp [hl,not_lt_of_gt hl]
    rw [hr,Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp [Finset.sum_add_distrib]
  have hs : (∑ i : Fin m, ∑ h : Fin m, if h < i then rowCollisionProbability X i h else 0) =
      ∑ i : Fin m, ∑ h : Fin m, if i < h then rowCollisionProbability X i h else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro h hh
    rw [rowCollisionProbability_symm X h i]
  unfold rowCollisionIntensity
  simp_rw [he]
  rw [Finset.sum_add_distrib,hs]
  ring

/-- Collision avoidance retains the elementary union lower bound. -/
theorem one_sub_rowAvoidance_le_intensity {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i = 1) :
    1-rowAvoidance X ≤ rowCollisionIntensity X := by
  classical
  let I := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2)
  have he : {z : Fin m → Fin n | ∃ a ∈ I, z a.1=z a.2} =
      {z | Function.Injective z}ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_compl_iff]
    constructor
    · rintro ⟨⟨i,h⟩,ha,hz⟩ hi
      exact (ne_of_lt (Finset.mem_filter.mp ha).2) (hi hz)
    · intro hz
      obtain ⟨i,h,hi,hne⟩ := Function.not_injective_iff.mp hz
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact ⟨(i,h),by simp [I,hl],hi⟩
      · exact ⟨(h,i),by simp [I,hl],hi.symm⟩
  have h := rowAssignmentEvent_union_bound X hX I
    (fun a z => z a.1=z a.2)
  rw [he,rowAssignmentEvent_compl,← rowAvoidance_eq_event] at h
  simp only [hs,Finset.prod_const_one] at h
  rw [rowCollisionIntensity_eq_sum_lt]
  convert h using 1
  simp only [I,Finset.sum_filter,Fintype.sum_prod_type,rowCollisionProbability]

end DittertRybin
