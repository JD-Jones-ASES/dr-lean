import DR.Endpoint.FiniteLocalLemma
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace DittertRybin.FiniteEvents.Tests
open scoped BigOperators

private noncomputable def weights (_ : Fin 4) : ℝ := 1/4
private def bits (e : Fin 2) (z : Fin 4) : Prop :=
  if e=0 then z.val<2 else z.val%2=0
private noncomputable def parameter (_ : Fin 2) : ℝ := 1/2
private def neighbors (_ : Fin 2) : Finset (Fin 2) := ∅

private theorem weights_nonneg (z : Fin 4) (_ : z ∈ Finset.univ) : 0 ≤ weights z := by
  norm_num [weights]
private theorem weights_sum : (∑ z : Fin 4, weights z)=1 := by
  norm_num [weights]
private theorem parameter_range (e : Fin 2) : 0 ≤ parameter e ∧ parameter e<1 := by
  norm_num [parameter]

private theorem bits_independent (e : Fin 2) (S : Finset (Fin 2)) (he : e ∉ S)
    (_ : Disjoint S (neighbors e)) :
    hitAvoidanceMass Finset.univ weights bits e S =
      mass Finset.univ weights (bits e)*avoidanceMass Finset.univ weights bits S := by
  fin_cases e <;> fin_cases S
  all_goals simp at he
  all_goals norm_num [hitAvoidanceMass,avoidanceMass,mass,indicator,bits,weights,Fin.sum_univ_succ]

private theorem bits_lll (e : Fin 2) : mass Finset.univ weights (bits e) ≤
    parameter e*(∏ f ∈ neighbors e, (1-parameter f)) := by
  fin_cases e <;>
    norm_num [neighbors,parameter,mass,indicator,weights,bits,Fin.sum_univ_succ]

-- Actual joint independence proves positive avoidance and all conditional bounds.
example (S : Finset (Fin 2)) : 0 < avoidanceMass Finset.univ weights bits S ∧
    ∀ e ∉ S, hitAvoidanceMass Finset.univ weights bits e S ≤
      (1/2)*avoidanceMass Finset.univ weights bits S :=
  finite_conditional_local_lemma Finset.univ weights bits neighbors parameter
    weights_nonneg weights_sum parameter_range bits_independent bits_lll S

example : (1/4:ℝ) ≤ avoidanceMass Finset.univ weights bits Finset.univ := by
  have h := finite_local_lemma_product Finset.univ weights bits neighbors parameter
    weights_nonneg weights_sum parameter_range bits_independent bits_lll Finset.univ
  norm_num [parameter,Fin.prod_univ_succ] at h
  exact h

-- The lower product bound is sharp for this independent model.
example : avoidanceMass Finset.univ weights bits Finset.univ = 1/4 := by
  norm_num [avoidanceMass,mass,indicator,weights,bits,Fin.forall_fin_succ,Fin.sum_univ_succ]

-- Pairwise labels alone cannot establish the dependency premise for duplicate events.
private def duplicate (_ : Fin 2) (z : Fin 4) : Prop := z.val<2
example : hitAvoidanceMass Finset.univ weights duplicate 0 {1} ≠
    mass Finset.univ weights (duplicate 0)*avoidanceMass Finset.univ weights duplicate {1} := by
  norm_num [hitAvoidanceMass,avoidanceMass,mass,indicator,weights,duplicate,Fin.sum_univ_succ]

-- Zero-probability events and zero x values remain in the event family.
example (S : Finset (Fin 2)) :
    0 < avoidanceMass Finset.univ weights (fun _ : Fin 2 => fun _ => False) S := by
  have h := finite_conditional_local_lemma Finset.univ weights
    (fun _ : Fin 2 => fun _ => False) neighbors (fun _ => 0)
    weights_nonneg weights_sum (fun _ => by norm_num)
    (by intros; simp [hitAvoidanceMass,mass,indicator])
    (by intro e; simp [mass,indicator]) S
  exact h.1

-- Strict x<1 is essential to the positivity statement.
example : ¬(0 ≤ (1:ℝ) ∧ (1:ℝ)<1) := by norm_num

-- The arbitrary-event extension uses the actual normalized avoidance mass.
example : mass Finset.univ weights (fun z => z=(3:Fin 4) ∧ ∀ e ∈ (Finset.univ : Finset (Fin 2)), ¬bits e z)*
      (∏ e : Fin 2, (1-parameter e)) ≤
    mass Finset.univ weights (fun z => z=(3:Fin 4))*avoidanceMass Finset.univ weights bits Finset.univ := by
  apply finite_local_lemma_event_bound Finset.univ weights bits neighbors parameter
    weights_nonneg weights_sum parameter_range bits_independent bits_lll
    (fun z => z=(3:Fin 4)) Finset.univ Finset.univ
  intro B hB
  have he : B=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact Finset.disjoint_left.mp hB he (Finset.mem_univ e)
  subst B
  simp [avoidanceMass,mass,weights]

#print axioms avoidanceMass_extend_lower
#print axioms finite_conditional_local_lemma
#print axioms finite_local_lemma_product
#print axioms finite_local_lemma_event_bound

end DittertRybin.FiniteEvents.Tests
