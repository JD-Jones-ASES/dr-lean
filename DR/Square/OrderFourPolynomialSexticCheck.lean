import DR.Square.OrderFourPolynomialSexticRolesCheck

namespace DittertRybin

set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

theorem orderFourSexticSeedList_sorted (s : Fin 224) :
    (orderFourSexticSeedList s).Pairwise (· ≤ ·) := by
  have h : ∀ t : Fin 224, (orderFourSexticSeedList t).Pairwise (· ≤ ·) := by decide +kernel
  exact h s

theorem orderFourCertificateCoefficient_seed (s : Fin 224) :
    orderFourCertificateCoefficient (orderFourSexticSeedCells s) =
      orderFourSexticExpectedCoefficient s := by
  change orderFourCertificateCoefficient (orderFourSexticSeedList s : Multiset (Fin 16)) = _
  rw [orderFourCertificateCoefficient_sorted_list _ (orderFourSexticSeedList_sorted s),
    orderFourSexticListCoefficient_eq_table s (orderFourSexticEntryKey s),
    orderFourSexticTableCoefficient_eq_expected]

end DittertRybin
