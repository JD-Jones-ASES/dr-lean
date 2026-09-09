import DR.Endpoint.FiniteAvoidance

/-! The finite asymmetric local lemma, proved by conditional-mass induction.
All bounds are cleared products. Positivity of avoidance is a conclusion,
including when some forbidden events have zero mass. The dependency premise
is joint nonneighbor independence, not pairwise independence. -/

namespace DittertRybin.FiniteEvents
open scoped BigOperators

variable {α ι : Type*} [DecidableEq ι]

/-- The finite conditional local lemma on arbitrary nonnegative finite weights. -/
theorem finite_conditional_local_lemma (Ω : Finset α) (w : α → ℝ)
    (E : ι → α → Prop) (N : ι → Finset ι) (x : ι → ℝ)
    (hw : ∀ z ∈ Ω, 0 ≤ w z) (hs : ∑ z ∈ Ω, w z=1)
    (hx : ∀ e, 0 ≤ x e ∧ x e < 1)
    (hind : ∀ e S, e ∉ S → Disjoint S (N e) →
      hitAvoidanceMass Ω w E e S = mass Ω w (E e)*avoidanceMass Ω w E S)
    (hlll : ∀ e, mass Ω w (E e) ≤ x e*(∏ f ∈ N e, (1 - x f)))
    (S : Finset ι) :
    0 < avoidanceMass Ω w E S ∧ ∀ e ∉ S,
      hitAvoidanceMass Ω w E e S ≤ x e*avoidanceMass Ω w E S := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  have hcond : ∀ e ∈ S, ∀ T ⊆ S, e ∉ T →
      hitAvoidanceMass Ω w E e T ≤ x e*avoidanceMass Ω w E T := by
    intro e he T hTS heT
    have hstrict : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hTS,by
      intro h; exact heT (h ▸ he)⟩
    exact (ih T hstrict).2 e heT
  have hpos : 0 < avoidanceMass Ω w E S := by
    by_cases hempty : S=∅
    · simp [hempty,hs]
    · obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hprev := ih (S.erase e) (Finset.erase_ssubset he)
      have hb := hprev.2 e (Finset.notMem_erase e S)
      have hp := mul_pos (sub_pos.mpr (hx e).2) hprev.1
      rw [← Finset.insert_erase he,avoidanceMass_insert]
      linarith
  refine ⟨hpos,?_⟩
  intro e heS
  let B := S \ N e
  have hBS : B ⊆ S := Finset.sdiff_subset
  have heB : e ∉ B := fun h => heS (hBS h)
  have hdisj : Disjoint B (N e) := Finset.sdiff_disjoint
  have hnum : hitAvoidanceMass Ω w E e S ≤
      mass Ω w (E e)*avoidanceMass Ω w E B := by
    apply (hitAvoidanceMass_antitone Ω w E hw e hBS).trans_eq
    exact hind e B heB hdisj
  have hden := avoidanceMass_extend_lower Ω w E x (fun f => (hx f).2.le) S B hBS hcond
  have hsub : S \ B ⊆ N e := by
    intro f hf
    have hfS := (Finset.mem_sdiff.mp hf).1
    have hfB := (Finset.mem_sdiff.mp hf).2
    by_contra hn
    exact hfB (Finset.mem_sdiff.mpr ⟨hfS,hn⟩)
  have hprod : (∏ f ∈ N e, (1 - x f)) ≤ ∏ f ∈ S \ B, (1 - x f) :=
    Finset.prod_le_prod_of_subset_of_le_one hsub
      (fun f _ => sub_nonneg.mpr (hx f).2.le)
      (fun f _ _ => by linarith [(hx f).1])
  have hB0 := avoidanceMass_nonneg Ω w E hw B
  calc
    hitAvoidanceMass Ω w E e S ≤ mass Ω w (E e)*avoidanceMass Ω w E B := hnum
    _ ≤ (x e*(∏ f ∈ N e, (1 - x f)))*avoidanceMass Ω w E B :=
      mul_le_mul_of_nonneg_right (hlll e) hB0
    _ ≤ (x e*(∏ f ∈ S \ B, (1 - x f)))*avoidanceMass Ω w E B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (hx e).1) hB0
    _ = x e*(avoidanceMass Ω w E B*(∏ f ∈ S \ B, (1 - x f))) := by ring
    _ ≤ x e*avoidanceMass Ω w E S := mul_le_mul_of_nonneg_left hden (hx e).1

/-- The explicit product lower bound follows from the proved conditional bounds. -/
theorem finite_local_lemma_product (Ω : Finset α) (w : α → ℝ)
    (E : ι → α → Prop) (N : ι → Finset ι) (x : ι → ℝ)
    (hw : ∀ z ∈ Ω, 0 ≤ w z) (hs : ∑ z ∈ Ω, w z=1)
    (hx : ∀ e, 0 ≤ x e ∧ x e < 1)
    (hind : ∀ e S, e ∉ S → Disjoint S (N e) →
      hitAvoidanceMass Ω w E e S = mass Ω w (E e)*avoidanceMass Ω w E S)
    (hlll : ∀ e, mass Ω w (E e) ≤ x e*(∏ f ∈ N e, (1 - x f)))
    (S : Finset ι) :
    (∏ e ∈ S, (1 - x e)) ≤ avoidanceMass Ω w E S := by
  have hcond : ∀ e ∈ S, ∀ T ⊆ S, e ∉ T →
      hitAvoidanceMass Ω w E e T ≤ x e*avoidanceMass Ω w E T := by
    intro e _ T _ heT
    exact (finite_conditional_local_lemma Ω w E N x hw hs hx hind hlll T).2 e heT
  have h := avoidanceMass_extend_lower Ω w E x (fun e => (hx e).2.le) S ∅
    (Finset.empty_subset S) hcond
  simpa only [Finset.sdiff_empty,avoidanceMass_empty,hs,one_mul] using h

/-- The conditional-distribution extension for an arbitrary event, with all
conditional denominators cleared. NF contains the forbidden events that
may depend on F; joint independence is required only outside NF. -/
theorem finite_local_lemma_event_bound (Ω : Finset α) (w : α → ℝ)
    (E : ι → α → Prop) (N : ι → Finset ι) (x : ι → ℝ)
    (hw : ∀ z ∈ Ω, 0 ≤ w z) (hs : ∑ z ∈ Ω, w z=1)
    (hx : ∀ e, 0 ≤ x e ∧ x e < 1)
    (hind : ∀ e S, e ∉ S → Disjoint S (N e) →
      hitAvoidanceMass Ω w E e S = mass Ω w (E e)*avoidanceMass Ω w E S)
    (hlll : ∀ e, mass Ω w (E e) ≤ x e*(∏ f ∈ N e, (1 - x f)))
    (F : α → Prop) (NF S : Finset ι)
    (hFind : ∀ B, Disjoint B NF →
      mass Ω w (fun z => F z ∧ ∀ e ∈ B, ¬E e z) =
        mass Ω w F*avoidanceMass Ω w E B) :
    mass Ω w (fun z => F z ∧ ∀ e ∈ S, ¬E e z)*
        (∏ e ∈ S ∩ NF, (1 - x e)) ≤ mass Ω w F*avoidanceMass Ω w E S := by
  classical
  let B := S \ NF
  have hBS : B ⊆ S := Finset.sdiff_subset
  have hcond : ∀ e ∈ S, ∀ T ⊆ S, e ∉ T →
      hitAvoidanceMass Ω w E e T ≤ x e*avoidanceMass Ω w E T := by
    intro e _ T _ heT
    exact (finite_conditional_local_lemma Ω w E N x hw hs hx hind hlll T).2 e heT
  have hden := avoidanceMass_extend_lower Ω w E x (fun e => (hx e).2.le) S B hBS hcond
  have hset : S \ B = S ∩ NF := by
    ext e
    simp only [B,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hset] at hden
  have hnum : mass Ω w (fun z => F z ∧ ∀ e ∈ S, ¬E e z) ≤
      mass Ω w F*avoidanceMass Ω w E B := by
    apply (mass_mono Ω w (fun z => F z ∧ ∀ e ∈ S, ¬E e z)
      (fun z => F z ∧ ∀ e ∈ B, ¬E e z) hw (fun z hz =>
        ⟨hz.1,fun e he => hz.2 e (hBS he)⟩)).trans_eq
    exact hFind B Finset.sdiff_disjoint
  have hp : 0 ≤ ∏ e ∈ S ∩ NF, (1 - x e) :=
    Finset.prod_nonneg fun e _ => sub_nonneg.mpr (hx e).2.le
  calc
    _ ≤ (mass Ω w F*avoidanceMass Ω w E B)*(∏ e ∈ S ∩ NF, (1 - x e)) :=
      mul_le_mul_of_nonneg_right hnum hp
    _ = mass Ω w F*(avoidanceMass Ω w E B*(∏ e ∈ S ∩ NF, (1 - x e))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (mass_nonneg Ω w F hw)

end DittertRybin.FiniteEvents
