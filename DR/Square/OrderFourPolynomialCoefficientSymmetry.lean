import DR.Square.OrderFourPolynomialSymmetry

namespace DittertRybin

open MvPolynomial

theorem orderFour_toFinsupp_map (s : Multiset (Fin 16)) (e : Equiv.Perm (Fin 16)) :
    (s.map e).toFinsupp = s.toFinsupp.mapDomain e := by
  apply Multiset.toFinsupp.symm.injective
  change Finsupp.toMultiset ((s.map e).toFinsupp) =
    Finsupp.toMultiset (s.toFinsupp.mapDomain e)
  rw [Multiset.toFinsupp_toMultiset, ← Finsupp.toMultiset_map,
    Multiset.toFinsupp_toMultiset]

theorem orderFour_coeff_physical (p : MvPolynomial (Fin 16) ℚ)
    (r c : Equiv.Perm (Fin 4))
    (hp : rename (orderFourPhysicalPermutation r c) p = p)
    (s : Multiset (Fin 16)) :
    coeff ((s.map (orderFourPhysicalPermutation r c)).toFinsupp) p = coeff s.toFinsupp p := by
  rw [orderFour_toFinsupp_map]
  conv_lhs => rw [← hp]
  exact coeff_rename_mapDomain _ (orderFourPhysicalPermutation r c).injective _ _

end DittertRybin
