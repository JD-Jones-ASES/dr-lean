import DR.Rectangular.FourRowMinorantTwo
import Mathlib.Logic.Equiv.Fintype

/-!
# Permutations and closed faces of the corrected four-row minorant

All relabelling statements are polynomial and allow signed coordinates. The
positivity statements retain the actual nonnegative probability simplices.
-/

namespace DittertRybin
open scoped BigOperators

theorem fourRow_complement_product_permute (r : Fin 4 → ℝ)
    (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    (∏ k ∈ (Finset.univ.erase i).erase j, (r ∘ e) k) =
      ∏ k ∈ (Finset.univ.erase (e i)).erase (e j), r k := by
  classical
  rw [fourRow_complement_product,fourRow_complement_product]
  calc
    _ = ∏ k, if e k ≠ e i ∧ e k ≠ e j then r (e k) else 1 := by
      simp only [Function.comp_apply,e.injective.ne_iff]
    _ = _ := Equiv.prod_comp e (fun k => if k ≠ e i ∧ k ≠ e j then r k else 1)

theorem fourRowMinorantHomogeneous_permute (r v : Fin 4 → ℝ)
    (e : Equiv.Perm (Fin 4)) :
    fourRowMinorantHomogeneous (r ∘ e) (v ∘ e) = fourRowMinorantHomogeneous r v := by
  classical
  unfold fourRowMinorantHomogeneous
  simp_rw [fourRowGaugeCollision_permute,fourRow_complement_product_permute,
    Function.comp_apply]
  rw [Equiv.sum_comp e r,Equiv.sum_comp e (fun i => v i*fourRowGaugeCollision r i)]
  congr 2
  have he (i : Fin 4) :
      (∑ j ∈ Finset.univ.erase i, v (e i)*v (e j)*
          ∏ k ∈ (Finset.univ.erase (e i)).erase (e j), r k) =
        ∑ j ∈ Finset.univ.erase (e i), v (e i)*v j*
          ∏ k ∈ (Finset.univ.erase (e i)).erase j, r k := by
    have h1 := Finset.sum_erase_add Finset.univ
      (fun j => v (e i)*v (e j)*∏ k ∈ (Finset.univ.erase (e i)).erase (e j), r k)
      (Finset.mem_univ i)
    have h2 := Finset.sum_erase_add Finset.univ
      (fun j => v (e i)*v j*∏ k ∈ (Finset.univ.erase (e i)).erase j, r k)
      (Finset.mem_univ (e i))
    rw [Equiv.sum_comp e (fun j => v (e i)*v j*
      ∏ k ∈ (Finset.univ.erase (e i)).erase j, r k)] at h1
    linarith
  simp_rw [he]
  exact Equiv.sum_comp e (fun i => ∑ j ∈ Finset.univ.erase i,
    v i*v j*∏ k ∈ (Finset.univ.erase i).erase j, r k)

/-- Every distribution supported on at most two designated coordinates satisfies
the minorant; the designated rows and their complements may all lie on the boundary. -/
theorem fourRowMinorantHomogeneous_pair_nonneg (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hsr : ∑ i, r i = 1)
    (hv : ∀ i, 0 ≤ v i) (hsv : ∑ i, v i = 1)
    (i j : Fin 4) (hij : i ≠ j) (hsupp : ∀ k, k ≠ i → k ≠ j → v k = 0) :
    0 ≤ fourRowMinorantHomogeneous r v := by
  classical
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair
    (![0,1] : Fin 2 → Fin 4) (![i,j] : Fin 2 → Fin 4)
    (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
    (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
  have he0 : e 0 = i := he 0
  have he1 : e 1 = j := he 1
  have hv2 : v (e 2) = 0 := hsupp _
    (by rw [←he0]; exact e.injective.ne (by decide))
    (by rw [←he1]; exact e.injective.ne (by decide))
  have hv3 : v (e 3) = 0 := hsupp _
    (by rw [←he0]; exact e.injective.ne (by decide))
    (by rw [←he1]; exact e.injective.ne (by decide))
  have hvs : v (e 0)+v (e 1)=1 := by
    have h := (Equiv.sum_comp e v).trans hsv
    simpa [Fin.sum_univ_succ,hv2,hv3] using h
  have hT1 : v (e 0) ≤ 1 := by linarith [hv (e 1)]
  have heqv : v ∘ e = ![v (e 0),1-v (e 0),0,0] := by
    funext k
    fin_cases k <;> simp [Function.comp_apply,Matrix.cons_val_two,Matrix.cons_val_three,
      hv2,hv3]
    linarith
  have heqr : r ∘ e = ![r (e 0),r (e 1),r (e 2),r (e 3)] := by
    funext k
    fin_cases k <;> simp [Function.comp_apply,Matrix.cons_val_two,Matrix.cons_val_three]
  have hrs : r (e 0)+r (e 1)+r (e 2)+r (e 3)=1 := by
    have h := (Equiv.sum_comp e r).trans hsr
    simp [Fin.sum_univ_succ] at h
    linarith
  have h := fourRowMinorantHomogeneous_two_nonneg (hr (e 0)) (hr (e 1))
    (hr (e 2)) (hr (e 3)) hrs (hv (e 0)) hT1
  rw [←heqr,←heqv,fourRowMinorantHomogeneous_permute] at h
  exact h

/-- With the last row zero, the objective is affine in the other three
column-distribution coordinates at fixed last coordinate. -/
theorem fourRowMinorantHomogeneous_zero_last_decomposition (r v : Fin 4 → ℝ)
    (hr3 : r 3 = 0) (hsv : ∑ i, v i = 1) :
    (1-v 3)*fourRowMinorantHomogeneous r v =
      v 0*fourRowMinorantHomogeneous r ![1-v 3,0,0,v 3]+
      v 1*fourRowMinorantHomogeneous r ![0,1-v 3,0,v 3]+
      v 2*fourRowMinorantHomogeneous r ![0,0,1-v 3,v 3] := by
  have hv0 : v 0 = 1-v 1-v 2-v 3 := by
    simp [Fin.sum_univ_succ] at hsv
    linarith
  norm_num [fourRowMinorantHomogeneous,fourRowGaugeCollision,fourRow_complement_product,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,Fin.ext_iff,
    -Fin.val_eq_zero_iff,Matrix.cons_val_two,Matrix.cons_val_three,hr3,hv0]
  simp only [show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl,hr3]
  ring

private theorem minorant_zero_last_nonneg (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hsr : ∑ i, r i = 1)
    (hv : ∀ i, 0 ≤ v i) (hsv : ∑ i, v i = 1) (hr3 : r 3 = 0) :
    0 ≤ fourRowMinorantHomogeneous r v := by
  have hvs : v 0+v 1+v 2+v 3=1 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hsv
  have hv3 : v 3 ≤ 1 := by linarith [hv 0,hv 1,hv 2]
  by_cases h3 : v 3 = 1
  · have h0 : v 0 = 0 := by linarith [hv 0,hv 1,hv 2]
    have h1 : v 1 = 0 := by linarith [hv 0,hv 1,hv 2]
    have h2 : v 2 = 0 := by linarith [hv 0,hv 1,hv 2]
    apply fourRowMinorantHomogeneous_pair_nonneg r v hr hsr hv hsv 0 3 (by decide)
    intro k hk0 hk3
    fin_cases k <;> simp_all
  have h3p : 0 < 1-v 3 := by exact sub_pos.mpr (lt_of_le_of_ne hv3 h3)
  have hA : 0 ≤ fourRowMinorantHomogeneous r ![1-v 3,0,0,v 3] := by
    refine fourRowMinorantHomogeneous_pair_nonneg r _ hr hsr ?_ ?_ 0 3 (by decide) ?_
    · intro k; fin_cases k
      · exact h3p.le
      · exact le_rfl
      · exact le_rfl
      · exact hv 3
    · norm_num [Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
    · intro k hk0 hk3; fin_cases k <;> first | contradiction | rfl
  have hB : 0 ≤ fourRowMinorantHomogeneous r ![0,1-v 3,0,v 3] := by
    refine fourRowMinorantHomogeneous_pair_nonneg r _ hr hsr ?_ ?_ 1 3 (by decide) ?_
    · intro k; fin_cases k
      · exact le_rfl
      · exact h3p.le
      · exact le_rfl
      · exact hv 3
    · norm_num [Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
    · intro k hk1 hk3; fin_cases k <;> first | contradiction | rfl
  have hC : 0 ≤ fourRowMinorantHomogeneous r ![0,0,1-v 3,v 3] := by
    refine fourRowMinorantHomogeneous_pair_nonneg r _ hr hsr ?_ ?_ 2 3 (by decide) ?_
    · intro k; fin_cases k
      · exact le_rfl
      · exact le_rfl
      · exact h3p.le
      · exact hv 3
    · norm_num [Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
    · intro k hk2 hk3; fin_cases k <;> first | contradiction | rfl
  have hmul : 0 ≤ (1-v 3)*fourRowMinorantHomogeneous r v := by
    rw [fourRowMinorantHomogeneous_zero_last_decomposition r v hr3 hsv]
    exact add_nonneg (add_nonneg (mul_nonneg (hv 0) hA) (mul_nonneg (hv 1) hB))
      (mul_nonneg (hv 2) hC)
  exact nonneg_of_mul_nonneg_right hmul h3p

/-- Every boundary row probability vector satisfies the corrected minorant,
for the entire closed column-distribution simplex. -/
theorem fourRowMinorantHomogeneous_boundary_nonneg (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hsr : ∑ i, r i = 1)
    (hv : ∀ i, 0 ≤ v i) (hsv : ∑ i, v i = 1) (hz : ∃ i, r i = 0) :
    0 ≤ fourRowMinorantHomogeneous r v := by
  classical
  obtain ⟨i,hi⟩ := hz
  let e := Equiv.swap (3 : Fin 4) i
  have h := minorant_zero_last_nonneg (r ∘ e) (v ∘ e)
    (fun j => hr (e j)) ((Equiv.sum_comp e r).trans hsr)
    (fun j => hv (e j)) ((Equiv.sum_comp e v).trans hsv)
    (by simp [e,Function.comp_apply,hi])
  rwa [fourRowMinorantHomogeneous_permute] at h

end DittertRybin
