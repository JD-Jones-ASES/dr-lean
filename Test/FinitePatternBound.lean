import DR.Endpoint.FinitePatternBound
import Mathlib.Algebra.BigOperators.Fin

namespace DittertRybin.FiniteEvents.Tests
open scoped BigOperators

private noncomputable def oneEventWeights (_ : Fin 2) : ℝ := 1/2
private def oneEvent (_ : Fin 1) (z : Fin 2) : Prop := z=0

private theorem oneEvent_independence (e : Fin 1) (S : Finset (Fin 1)) (he : e ∉ S)
    (_ : Disjoint S ∅) :
    hitAvoidanceMass Finset.univ oneEventWeights oneEvent e S =
      mass Finset.univ oneEventWeights (oneEvent e)*avoidanceMass Finset.univ oneEventWeights oneEvent S := by
  have hS : S=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    exact he ((Subsingleton.elim f e) ▸ hf)
  subst S
  simp [hitAvoidanceMass,avoidanceMass,mass,oneEventWeights]

-- F is the forbidden event itself, and its edge is removed from avoidance.
-- The restored factor is essential even for this one-event probability space.
example : mass Finset.univ oneEventWeights (fun z => z=0)*
    (∏ _e : Fin 1, (1-(1/2:ℝ))) ≤
      mass Finset.univ oneEventWeights (fun z => z=0)*
        avoidanceMass Finset.univ oneEventWeights oneEvent Finset.univ := by
  have h := finite_local_lemma_removed_events_bound Finset.univ oneEventWeights oneEvent
    (fun _ => ∅) (fun _ => 1/2) (by intro z hz; norm_num [oneEventWeights])
    (by norm_num [oneEventWeights]) (by intro e; norm_num) oneEvent_independence
    (by intro e; norm_num [mass,indicator,oneEvent,oneEventWeights,Fin.sum_univ_two])
    (fun z => z=0) Finset.univ Finset.univ Finset.univ (Finset.Subset.refl _)
    (Finset.Subset.refl _) (by
      intro B hB
      have he : B=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        exact Finset.disjoint_left.mp hB he (Finset.mem_univ e)
      subst B
      simp [avoidanceMass,mass,oneEventWeights])
  simpa only [Finset.sdiff_self,Finset.notMem_empty,false_implies,forall_const,and_true,
    Finset.univ_inter] using h

example : ¬(mass Finset.univ oneEventWeights (fun z => z=0) ≤
    mass Finset.univ oneEventWeights (fun z => z=0)*
      avoidanceMass Finset.univ oneEventWeights oneEvent Finset.univ) := by
  norm_num [mass,indicator,avoidanceMass,oneEventWeights,oneEvent,Fin.sum_univ_succ,Fin.forall_fin_succ]

#print axioms finite_local_lemma_removed_events_bound
end DittertRybin.FiniteEvents.Tests
