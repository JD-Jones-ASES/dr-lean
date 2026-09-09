import DR.Endpoint.FiniteLocalLemma

/-! Restore the local-lemma product for forbidden events removed from a
conditioning family. This is the denominator step for exact collision
patterns; the prescribed event need not avoid its internal edges. -/

namespace DittertRybin.FiniteEvents
open scoped BigOperators
variable {α ι : Type*} [DecidableEq ι]

/-- Removing L from the avoidance family costs the full neighborhood
product, including L itself. No internal event is silently conditioned away. -/
theorem finite_local_lemma_removed_events_bound (Ω : Finset α) (w : α → ℝ)
    (E : ι → α → Prop) (N : ι → Finset ι) (x : ι → ℝ)
    (hw : ∀ z ∈ Ω, 0 ≤ w z) (hs : ∑ z ∈ Ω, w z=1)
    (hx : ∀ e, 0 ≤ x e ∧ x e < 1)
    (hind : ∀ e S, e ∉ S → Disjoint S (N e) →
      hitAvoidanceMass Ω w E e S = mass Ω w (E e)*avoidanceMass Ω w E S)
    (hlll : ∀ e, mass Ω w (E e) ≤ x e*(∏ f ∈ N e, (1-x f)))
    (F : α → Prop) (NF T L : Finset ι) (hLT : L ⊆ T) (hLN : L ⊆ NF)
    (hFind : ∀ B, Disjoint B NF →
      mass Ω w (fun z => F z ∧ ∀ e ∈ B, ¬E e z) =
        mass Ω w F*avoidanceMass Ω w E B) :
    mass Ω w (fun z => F z ∧ ∀ e ∈ T \ L, ¬E e z)*
      (∏ e ∈ T ∩ NF, (1-x e)) ≤ mass Ω w F*avoidanceMass Ω w E T := by
  classical
  have hnum := finite_local_lemma_event_bound Ω w E N x hw hs hx hind hlll
    F NF (T \ L) hFind
  have hcond : ∀ e ∈ T, ∀ S ⊆ T, e ∉ S →
      hitAvoidanceMass Ω w E e S ≤ x e*avoidanceMass Ω w E S := by
    intro e _ S _ he
    exact (finite_conditional_local_lemma Ω w E N x hw hs hx hind hlll S).2 e he
  have hden := avoidanceMass_extend_lower Ω w E x (fun e => (hx e).2.le)
    T (T \ L) Finset.sdiff_subset hcond
  have hdiff : T \ (T \ L)=L := by
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · tauto
    · intro he; exact ⟨hLT he,by tauto⟩
  rw [hdiff] at hden
  have hdisj : Disjoint ((T \ L) ∩ NF) L := by
    apply Finset.disjoint_left.mpr
    intro e he heL
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).1).2 heL
  have hunion : ((T \ L) ∩ NF) ∪ L=T ∩ NF := by
    ext e
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    constructor
    · rintro (⟨⟨heT,_⟩,heN⟩ | heL)
      · exact ⟨heT,heN⟩
      · exact ⟨hLT heL,hLN heL⟩
    · tauto
  have hprod : (∏ e ∈ T ∩ NF, (1-x e)) =
      (∏ e ∈ (T \ L) ∩ NF, (1-x e))*(∏ e ∈ L, (1-x e)) := by
    rw [← hunion,Finset.prod_union hdisj]
  have hpL : 0 ≤ ∏ e ∈ L, (1-x e) :=
    Finset.prod_nonneg (fun e _ => sub_nonneg.mpr (hx e).2.le)
  rw [hprod,← mul_assoc]
  calc
    _ ≤ (mass Ω w F*avoidanceMass Ω w E (T \ L))*(∏ e ∈ L, (1-x e)) :=
      mul_le_mul_of_nonneg_right hnum hpL
    _ = mass Ω w F*(avoidanceMass Ω w E (T \ L)*(∏ e ∈ L, (1-x e))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (mass_nonneg Ω w F hw)

end DittertRybin.FiniteEvents
