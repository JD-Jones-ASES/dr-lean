import DR.Rectangular.FourRowMinorantRowPermutation
import DR.Rectangular.FourRowMinorantOneLarge

/-!
# Fixed-q feasible row maxima have one large coordinate

Sorting is used only after the actual maximum and feasibility predicates have
been transported through permutations. Triple rotations force equality of the
three smaller coordinates and exclude a repeated largest value directly.
-/

namespace DittertRybin
open scoped BigOperators

theorem IsFourRowMinorantRowMaximum.sorted_small_eq {γ : ℝ} {r : Fin 4 → ℝ}
    (hmax : IsFourRowMinorantRowMaximum γ r) (hγ : 0<γ)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1) (hv : ∀ i,0<fourRowMinorantStationary r i)
    (hq : 1/4<fourRowMinorantSquareSum r) (hm : Monotone r) : r 0=r 1 ∧ r 1=r 2 := by
  have h03 : r 0<r 3 := by
    by_contra h
    have heq : r 3=r 0 := le_antisymm (le_of_not_gt h) (hm (by decide))
    have hall : r=(fun _ => r 0) := by
      funext i
      exact le_antisymm ((hm (show i≤3 by omega)).trans_eq heq) (hm (by omega))
    have hs' := hs
    have hq' := hq
    rw [hall] at hs' hq'
    norm_num [fourRowMinorantSquareSum] at hs' hq'
    nlinarith
  have h23 : r 2≠r 3 := by
    intro h23
    let e := fourRowMinorantLargestPermutation
    have hloc := (hmax.permute e).triple_localMax hγ (fun i => hr (e i))
      ((Equiv.sum_comp e r).trans hs)
      (fun i => by rw [fourRowMinorantStationary_permute]; exact hv (e i))
    have htriple : (fun j : Fin 3 => (r ∘ e) j.castSucc)=![r 3,r 3,r 0] := by
      funext j
      fin_cases j <;> simp [e,fourRowMinorantLargestPermutation,Function.comp_apply,
        Matrix.cons_val_two,h23]
    rw [htriple] at hloc
    exact threeMomentCurve_not_localMax_repeated_larger h03 hloc
  have he02 : r 0=r 2 := by
    let e := fourRowMinorantTriplePermutation
    have hrep := (hmax.permute e).triple_repeated hγ (fun i => hr (e i))
      ((Equiv.sum_comp e r).trans hs)
      (fun i => by rw [fourRowMinorantStationary_permute]; exact hv (e i))
    have hrep' : r 0=r 2 ∨ r 0=r 3 ∨ r 2=r 3 := by
      simpa [e,fourRowMinorantTriplePermutation,Function.comp_apply,
        Matrix.cons_val_two,Matrix.cons_val_three] using hrep
    exact hrep'.resolve_right (fun h => h.elim (fun h => h03.ne h) h23)
  have h01 : r 0=r 1 := le_antisymm (hm (by decide)) ((hm (by decide : (1:Fin 4)≤2)).trans_eq he02.symm)
  exact ⟨h01,h01.symm.trans he02⟩

/-- A true fixed-q feasible maximum has the one-large-row form; no optimizer shape is assumed. -/
theorem IsFourRowMinorantRowMaximum.one_large {γ : ℝ} {r : Fin 4 → ℝ}
    (hmax : IsFourRowMinorantRowMaximum γ r) (hγ : 0<γ)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1) (hv : ∀ i,0<fourRowMinorantStationary r i)
    (hq0 : 1/4<fourRowMinorantSquareSum r) (hq1 : fourRowMinorantSquareSum r<1/3) :
    ∃ (R : ℝ) (e : Equiv.Perm (Fin 4)), 1/4<R ∧ R<1/2 ∧
      r ∘ e=fourRowMinorantOneLargeRows R := by
  let e := Tuple.sort r
  let u := r ∘ e
  have hum : Monotone u := Tuple.monotone_sort r
  have hus : (∑ i,u i)=1 := (Equiv.sum_comp e r).trans hs
  have huq : fourRowMinorantSquareSum u=fourRowMinorantSquareSum r :=
    fourRowMinorantSquareSum_permute r e
  have hup : ∀ i,0<u i := fun i => hr (e i)
  have huv : ∀ i,0<fourRowMinorantStationary u i := by
    intro i
    rw [fourRowMinorantStationary_permute]
    exact hv (e i)
  obtain ⟨h01,h12⟩ := (hmax.permute e).sorted_small_eq hγ hup hus huv (by rwa [huq]) hum
  let R := u 3
  let B := u 0
  have hu : u=![B,B,B,R] := by
    funext i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
    · rfl
  have hmass : 3*B+R=1 := by
    rw [hu] at hus
    norm_num [Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three] at hus
    linarith
  have hb : B=(1-R)/3 := by linarith
  have hBR : B<R := by
    have hle : B≤R := hum (by decide)
    by_contra h
    have he : B=R := le_antisymm hle (le_of_not_gt h)
    have hq := hq0
    rw [← huq,hu] at hq
    norm_num [fourRowMinorantSquareSum,Fin.sum_univ_four,Matrix.cons_val_two,
      Matrix.cons_val_three,he] at hq
    nlinarith
  have hR0 : 1/4<R := by linarith
  have hR1 : R<1/2 := by
    have hq := hq1
    rw [← huq,hu] at hq
    norm_num [fourRowMinorantSquareSum,Fin.sum_univ_four,Matrix.cons_val_two,
      Matrix.cons_val_three,hb] at hq
    by_contra h
    have hR : 1/2≤R := le_of_not_gt h
    nlinarith [sq_nonneg (R-1/2)]
  refine ⟨R,(Equiv.swap (0:Fin 4) 3).trans e,hR0,hR1,?_⟩
  change u ∘ Equiv.swap (0:Fin 4) 3=fourRowMinorantOneLargeRows R
  rw [hu]
  funext i
  fin_cases i <;> norm_num [Function.comp_apply,Equiv.swap_apply_def,
    fourRowMinorantOneLargeRows,Matrix.cons_val_two,Matrix.cons_val_three,hb,Fin.ext_iff]

end DittertRybin
