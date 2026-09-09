import DR.Square.OrderFourOrbitSextic

/-!
# The exact finite coefficient reduction

For degree-six polynomials invariant under physical row and column
permutations, the 224 physical seed coefficients determine every coefficient.
The reduction retains the finite equality premise for discharge by the
separate coefficient-check modules.
-/

namespace DittertRybin

open MvPolynomial

theorem orderFourSextic_polynomial_ext
    (p q : MvPolynomial (Fin 16) ℚ) (hp : p.IsHomogeneous 6) (hq : q.IsHomogeneous 6)
    (hpr : ∀ r c : Equiv.Perm (Fin 4), rename (orderFourPhysicalPermutation r c) p = p)
    (hqr : ∀ r c : Equiv.Perm (Fin 4), rename (orderFourPhysicalPermutation r c) q = q)
    (hseed : ∀ s : Fin 224, coeff (orderFourSexticSeedCells s).toFinsupp p =
      coeff (orderFourSexticSeedCells s).toFinsupp q) : p = q := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d.degree = 6
  · have hcard : d.toMultiset.card = 6 := by
      rw [Finsupp.card_toMultiset]
      exact hd
    obtain ⟨s,r,c,hs⟩ := orderFourSextic_multiset_orbit d.toMultiset hcard
    rw [← Finsupp.toMultiset_toFinsupp d, ← hs,
      orderFour_coeff_physical p r c (hpr r c),
      orderFour_coeff_physical q r c (hqr r c)]
    exact hseed s
  · rw [hp.coeff_eq_zero hd, hq.coeff_eq_zero hd]

end DittertRybin
