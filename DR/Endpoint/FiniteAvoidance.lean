import DR.Collision.Bonferroni
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Finite weighted avoidance identities and complement-product chaining.
These are the elementary algebra used in the conditional local lemma;
no positivity of an avoidance probability is presumed. -/

namespace DittertRybin.FiniteEvents
open scoped BigOperators

variable {α ι : Type*}

noncomputable def avoidanceMass (Ω : Finset α) (w : α → ℝ) (E : ι → α → Prop)
    (S : Finset ι) : ℝ := mass Ω w (fun z => ∀ e ∈ S, ¬E e z)

noncomputable def hitAvoidanceMass (Ω : Finset α) (w : α → ℝ) (E : ι → α → Prop)
    (e : ι) (S : Finset ι) : ℝ := mass Ω w (fun z => E e z ∧ ∀ f ∈ S, ¬E f z)

theorem mass_mono (Ω : Finset α) (w : α → ℝ) (E F : α → Prop)
    (hw : ∀ z ∈ Ω, 0 ≤ w z) (hEF : ∀ z, E z → F z) :
    mass Ω w E ≤ mass Ω w F := by
  classical
  apply Finset.sum_le_sum
  intro z hz
  apply mul_le_mul_of_nonneg_left _ (hw z hz)
  by_cases he : E z
  · simp [indicator,he,hEF z he]
  · have h := indicator_nonneg (F z)
    simpa only [indicator,if_neg he] using h

theorem avoidanceMass_nonneg (Ω : Finset α) (w : α → ℝ) (E : ι → α → Prop)
    (hw : ∀ z ∈ Ω, 0 ≤ w z) (S : Finset ι) : 0 ≤ avoidanceMass Ω w E S :=
  mass_nonneg Ω w _ hw

theorem hitAvoidanceMass_nonneg (Ω : Finset α) (w : α → ℝ) (E : ι → α → Prop)
    (hw : ∀ z ∈ Ω, 0 ≤ w z) (e : ι) (S : Finset ι) :
    0 ≤ hitAvoidanceMass Ω w E e S := mass_nonneg Ω w _ hw

@[simp] theorem avoidanceMass_empty (Ω : Finset α) (w : α → ℝ) (E : ι → α → Prop) :
    avoidanceMass Ω w E ∅ = ∑ z ∈ Ω, w z := by
  simp [avoidanceMass,mass]

@[simp] theorem hitAvoidanceMass_empty (Ω : Finset α) (w : α → ℝ) (E : ι → α → Prop)
    (e : ι) : hitAvoidanceMass Ω w E e ∅ = mass Ω w (E e) := by
  simp [hitAvoidanceMass,mass]

theorem hitAvoidanceMass_antitone (Ω : Finset α) (w : α → ℝ) (E : ι → α → Prop)
    (hw : ∀ z ∈ Ω, 0 ≤ w z) (e : ι) {S T : Finset ι} (hST : S ⊆ T) :
    hitAvoidanceMass Ω w E e T ≤ hitAvoidanceMass Ω w E e S := by
  apply mass_mono Ω w _ _ hw
  intro z hz
  exact ⟨hz.1,fun f hf => hz.2 f (hST hf)⟩

/-- Appending one forbidden event subtracts exactly its remaining mass. -/
theorem avoidanceMass_insert [DecidableEq ι] (Ω : Finset α) (w : α → ℝ)
    (E : ι → α → Prop) (e : ι) (S : Finset ι) :
    avoidanceMass Ω w E (insert e S) =
      avoidanceMass Ω w E S-hitAvoidanceMass Ω w E e S := by
  classical
  unfold avoidanceMass hitAvoidanceMass mass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases he : E e z <;> by_cases ha : ∀ f ∈ S, ¬E f z <;>
    simp [indicator,he,ha]

/-- Chaining conditional upper bounds gives a complement-product lower bound.
The required bounds concern proper subsets of S, since e is omitted from T. -/
theorem avoidanceMass_extend_lower [DecidableEq ι] (Ω : Finset α) (w : α → ℝ)
    (E : ι → α → Prop) (x : ι → ℝ) (hx : ∀ e, x e ≤ 1) (S B : Finset ι)
    (hBS : B ⊆ S)
    (hcond : ∀ e ∈ S, ∀ T ⊆ S, e ∉ T →
      hitAvoidanceMass Ω w E e T ≤ x e*avoidanceMass Ω w E T) :
    avoidanceMass Ω w E B*(∏ e ∈ S \ B, (1 - x e)) ≤ avoidanceMass Ω w E S := by
  classical
  have aux : ∀ A : Finset ι, Disjoint A B → A ∪ B ⊆ S →
      avoidanceMass Ω w E B*(∏ e ∈ A, (1 - x e)) ≤ avoidanceMass Ω w E (A ∪ B) := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _ _; simp
    | @insert e A he ih =>
      intro hd hsub
      have heB : e ∉ B := (Finset.disjoint_insert_left.mp hd).1
      have hAB : Disjoint A B := (Finset.disjoint_insert_left.mp hd).2
      have hsmall : A ∪ B ⊆ S := by
        intro f hf
        exact hsub (Finset.mem_union.mpr (by
          rcases Finset.mem_union.mp hf with hf | hf
          · exact Or.inl (Finset.mem_insert_of_mem hf)
          · exact Or.inr hf))
      have hstage := ih hAB hsmall
      have heS : e ∈ S := hsub (by simp)
      have heT : e ∉ A ∪ B := by simp [he,heB]
      have hb := hcond e heS (A ∪ B) hsmall heT
      have hstep : (1-x e)*avoidanceMass Ω w E (A ∪ B) ≤
          avoidanceMass Ω w E (insert e (A ∪ B)) := by
        rw [avoidanceMass_insert]
        linarith
      rw [Finset.insert_union,Finset.prod_insert he]
      calc
        _ = (1-x e)*(avoidanceMass Ω w E B*∏ f ∈ A, (1 - x f)) := by ring
        _ ≤ (1-x e)*avoidanceMass Ω w E (A ∪ B) :=
          mul_le_mul_of_nonneg_left hstage (sub_nonneg.mpr (hx e))
        _ ≤ _ := hstep
  have h := aux (S \ B) Finset.sdiff_disjoint (by simp [Finset.sdiff_union_of_subset hBS])
  simpa only [Finset.sdiff_union_of_subset hBS] using h

end DittertRybin.FiniteEvents
