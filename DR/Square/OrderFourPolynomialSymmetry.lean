import DR.Square.OrderFourPolynomialCertificate
import DR.Compactness
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Physical symmetry of the actual gap and the certificate polynomial

The polynomial symmetry is proved over all real inputs. It therefore remains
valid on boundary faces and at every coefficient, before any probability
normalization or positivity hypothesis.
-/

namespace DittertRybin

open Certificates MvPolynomial
open scoped BigOperators

set_option maxRecDepth 10000

theorem orderFour_rationalEval_ext {p q : MvPolynomial (Fin 16) ℚ}
    (h : ∀ x : Fin 16 → ℝ, rationalEval x p = rationalEval x q) : p = q := by
  apply MvPolynomial.map_injective (f := Rat.castHom ℝ) (Rat.cast_injective)
  apply MvPolynomial.funext
  intro x
  simpa only [rationalEval, eval_map] using h x

theorem orderFourPhysicalPermutation_cell (r c : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    orderFourPhysicalPermutation r c (orderFourCell (i,j)) = orderFourCell (r i,c j) := by
  apply Fin.ext
  change orderFourCellMapNat r c (orderFourCell (i,j)).val = (orderFourCell (r i,c j)).val
  rw [orderFourCell_val, orderFourCell_val]
  have hd : (4*i.val+j.val)/4 = i.val := by omega
  have hm : (4*i.val+j.val)%4 = j.val := by omega
  simp [orderFourCellMapNat, hd, hm, orderFourExtendLabel, i.isLt, j.isLt]

theorem orderFourUnflat_physical (r c : Equiv.Perm (Fin 4)) (x : Fin 16 → ℝ) :
    orderFourUnflat (x ∘ orderFourPhysicalPermutation r c) =
      fun i j => orderFourUnflat x (r i) (c j) := by
  funext i j
  simp [orderFourUnflat, Function.comp_apply, orderFourPhysicalPermutation_cell]

theorem orderFourQuarticPolynomial_rename (r c : Equiv.Perm (Fin 4)) :
    rename (orderFourPhysicalPermutation r c) orderFourQuarticPolynomial =
      orderFourQuarticPolynomial := by
  apply orderFour_rationalEval_ext
  intro x
  simp only [rationalEval, eval₂_rename]
  change rationalEval (x ∘ orderFourPhysicalPermutation r c) orderFourQuarticPolynomial =
    rationalEval x orderFourQuarticPolynomial
  rw [orderFourQuarticPolynomial_eval, orderFourQuarticPolynomial_eval,
    orderFourUnflat_physical, separationProbability_permute]

theorem orderFourSexticGapPolynomial_rename (r c : Equiv.Perm (Fin 4)) :
    rename (orderFourPhysicalPermutation r c) orderFourSexticGapPolynomial =
      orderFourSexticGapPolynomial := by
  apply orderFour_rationalEval_ext
  intro x
  simp only [rationalEval, eval₂_rename]
  change rationalEval (x ∘ orderFourPhysicalPermutation r c) orderFourSexticGapPolynomial =
    rationalEval x orderFourSexticGapPolynomial
  rw [orderFourSexticGapPolynomial_eval, orderFourSexticGapPolynomial_eval,
    orderFourUnflat_physical, separationProbability_permute]
  simp only [Function.comp_apply, Equiv.sum_comp]

theorem orderFourSortedMultiplier_map_perm (s : Sym (Fin 16) 4)
    (r c : Equiv.Perm (Fin 4)) :
    (orderFourSortedMultiplier (s.map (orderFourPhysicalPermutation r c))).toList.Perm
      ((orderFourSortedMultiplier s).map (orderFourCellMapNat r c)).toList := by
  apply Multiset.coe_eq_coe.mp
  simp only [Vector.toList_map, orderFourSortedMultiplier_toList,
    ← Multiset.map_coe, Multiset.sort_eq, Sym.val_eq_coe, Sym.coe_map,
    Multiset.map_map]
  rfl

theorem orderFourSortedMultiplierMatrix_physical (s : Sym (Fin 16) 4)
    (r c : Equiv.Perm (Fin 4)) :
    (orderFourMultiplierMatrix (orderFourSortedMultiplier
      (s.map (orderFourPhysicalPermutation r c)))).submatrix
        (orderFourPhysicalPermutation r c) (orderFourPhysicalPermutation r c) =
      orderFourMultiplierMatrix (orderFourSortedMultiplier s) := by
  rw [orderFourMultiplierMatrix_perm (orderFourSortedMultiplier_map_perm s r c)]
  exact orderFourMultiplierMatrix_physical r c (orderFourSortedMultiplier s)

theorem orderFourMultiplierValue_map (s : Sym (Fin 16) 4)
    (e : Equiv.Perm (Fin 16)) (x : Fin 16 → ℝ) :
    orderFourMultiplierValue (s.map e) x = orderFourMultiplierValue s (x ∘ e) := by
  simp only [orderFourMultiplierValue, Sym.val_eq_coe, Sym.coe_map, Multiset.map_map]

theorem orderFourSortedMultiplier_quadratic_physical (s : Sym (Fin 16) 4)
    (r c : Equiv.Perm (Fin 4)) (x : Fin 16 → ℝ) :
    quadraticValue ((orderFourMultiplierMatrix (orderFourSortedMultiplier s)).map
      (fun q : ℚ => (q : ℝ))) (x ∘ orderFourPhysicalPermutation r c) =
    quadraticValue ((orderFourMultiplierMatrix (orderFourSortedMultiplier
      (s.map (orderFourPhysicalPermutation r c)))).map (fun q : ℚ => (q : ℝ))) x := by
  have h := orderFourSortedMultiplierMatrix_physical s r c
  have hreal := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℚ =>
    M.map (fun q : ℚ => (q : ℝ))) h
  change (((orderFourMultiplierMatrix (orderFourSortedMultiplier
    (s.map (orderFourPhysicalPermutation r c)))).map (fun q : ℚ => (q : ℝ))).submatrix
      (orderFourPhysicalPermutation r c) (orderFourPhysicalPermutation r c)) = _ at hreal
  rw [← hreal]
  exact orderFour_quadraticValue_submatrix _ _ x

theorem orderFourCertificatePolynomial_rename (r c : Equiv.Perm (Fin 4)) :
    rename (orderFourPhysicalPermutation r c) orderFourCertificatePolynomial =
      orderFourCertificatePolynomial := by
  apply orderFour_rationalEval_ext
  intro x
  simp only [rationalEval, eval₂_rename]
  change rationalEval (x ∘ orderFourPhysicalPermutation r c) orderFourCertificatePolynomial =
    rationalEval x orderFourCertificatePolynomial
  rw [orderFourCertificatePolynomial_eval, orderFourCertificatePolynomial_eval]
  simp_rw [← orderFourMultiplierValue_map, orderFourSortedMultiplier_quadratic_physical]
  exact Equiv.sum_comp (Sym.equivCongr (orderFourPhysicalPermutation r c))
    (fun s => orderFourMultiplierValue s x * quadraticValue
      ((orderFourMultiplierMatrix (orderFourSortedMultiplier s)).map
        (fun q : ℚ => (q : ℝ))) x)

end DittertRybin
