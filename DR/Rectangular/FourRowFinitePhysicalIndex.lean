import DR.Rectangular.FourRowFinitePairIndex
import DR.Certificates.FiniteTripleSeeds

/-! Actual finite-host labels for the distinguished and ordinary seed indices.
These equivalences apply to any ambient dimensions at least three. -/

namespace DittertRybin
open Certificates
noncomputable section

def fourRowFinitePhysicalAxisEquiv {m r : ℕ} (hr : r ≤ m) :
    Fin r ⊕ Fin (m-r) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hr))

theorem fourRowFinitePhysicalAxisEquiv_inl {m r : ℕ} (hr : r ≤ m) (i : Fin r) :
    (fourRowFinitePhysicalAxisEquiv hr (.inl i)).val = i.val := rfl

theorem fourRowFinitePhysicalAxisEquiv_inr {m r : ℕ} (hr : r ≤ m) (i : Fin (m-r)) :
    (fourRowFinitePhysicalAxisEquiv hr (.inr i)).val = r+i.val := rfl

def fourRowFiniteSeedPhysicalEquiv {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (s : Fin 10) :
    ((Fin (fourRowFiniteSeedRows s) ⊕ Fin (m-fourRowFiniteSeedRows s)) ×
      (Fin (fourRowFiniteSeedColumns s) ⊕ Fin (n-fourRowFiniteSeedColumns s))) ≃ Fin m × Fin n :=
  Equiv.prodCongr
    (fourRowFinitePhysicalAxisEquiv ((fourRowFiniteSeed_counts s).2.2.1.trans hm))
    (fourRowFinitePhysicalAxisEquiv ((fourRowFiniteSeed_counts s).2.2.2.2.trans hn))

theorem fourRowFiniteTripleSeed_label_bounds : ∀ (s : Fin 10) (i : Fin 3),
    (finiteTripleSeed s i).1.val < fourRowFiniteSeedRows s ∧
      (finiteTripleSeed s i).2.val < fourRowFiniteSeedColumns s := by
  decide +kernel

def fourRowFiniteTripleSeedRow (s : Fin 10) (i : Fin 3) : Fin (fourRowFiniteSeedRows s) :=
  ⟨(finiteTripleSeed s i).1.val,(fourRowFiniteTripleSeed_label_bounds s i).1⟩

def fourRowFiniteTripleSeedColumn (s : Fin 10) (i : Fin 3) : Fin (fourRowFiniteSeedColumns s) :=
  ⟨(finiteTripleSeed s i).2.val,(fourRowFiniteTripleSeed_label_bounds s i).2⟩

theorem fourRowFiniteSeedPhysicalEquiv_seed {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (s : Fin 10) (i : Fin 3) :
    fourRowFiniteSeedPhysicalEquiv hm hn s
      (.inl (fourRowFiniteTripleSeedRow s i),.inl (fourRowFiniteTripleSeedColumn s i)) =
      finiteTriplePhysicalSeed hm hn s i := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

end
end DittertRybin
