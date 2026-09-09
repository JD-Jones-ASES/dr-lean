import DR.Certificates.FiniteTupleRelabeling
import DR.Rectangular.FourRowFiniteSeeds

/-! Complete physical coverage of the ten multiplier-triple seeds.
The proof checks all25 row/column equality-pattern pairs and constructs
permutations of the actual finite row and column hosts. -/
namespace DittertRybin.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def threeTuplePatterns : Fin 5 → (Fin 3 → Fin 3) :=
  ![![0,0,0],![0,0,2],![0,1,0],![0,1,1],![0,1,2]]

theorem threeTuplePatterns_complete : ∀ p : Fin 3 → Fin 3,
    IsTuplePattern p → ∃ r : Fin 5, threeTuplePatterns r = p := by
  decide +kernel

def finiteTripleOrder : Fin 6 → (Fin 3 → Fin 3) :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]]

theorem finiteTripleOrder_bijective : ∀ q : Fin 6, Function.Bijective (finiteTripleOrder q) := by
  decide +kernel

def finiteTripleSeed : Fin 10 → (Fin 3 → Fin 3 × Fin 3) :=
  ![![(0,0),(0,0),(0,0)],
    ![(0,0),(0,0),(0,1)],
    ![(0,0),(0,0),(1,0)],
    ![(0,0),(0,0),(1,1)],
    ![(0,0),(0,1),(0,2)],
    ![(0,0),(0,1),(1,0)],
    ![(0,0),(0,1),(1,2)],
    ![(0,0),(1,0),(2,0)],
    ![(0,0),(1,0),(2,1)],
    ![(0,0),(1,1),(2,2)]]

theorem finiteTripleSeed_mark : ∀ a : Fin 10,
    List.ofFn (fun i => ((finiteTripleSeed a i).1.val,(finiteTripleSeed a i).2.val)) =
      fourRowFiniteSeedMark a := by
  decide +kernel

theorem finiteTripleSeed_pattern_coverage : ∀ r c : Fin 5,
    ∃ a : Fin 10, ∃ q : Fin 6,
      (∀ i j : Fin 3, threeTuplePatterns r (finiteTripleOrder q i) =
        threeTuplePatterns r (finiteTripleOrder q j) ↔
          (finiteTripleSeed a i).1 = (finiteTripleSeed a j).1) ∧
      (∀ i j : Fin 3, threeTuplePatterns c (finiteTripleOrder q i) =
        threeTuplePatterns c (finiteTripleOrder q j) ↔
          (finiteTripleSeed a i).2 = (finiteTripleSeed a j).2) := by
  decide +kernel

def finiteTriplePhysicalSeed {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (a : Fin 10) (i : Fin 3) : Fin m × Fin n :=
  (Fin.castLE hm (finiteTripleSeed a i).1, Fin.castLE hn (finiteTripleSeed a i).2)

/-- Every actual multiplier triple is one of the ten literal seeds after
position, row and column permutations. Repeated cells remain literal repetitions. -/
theorem finiteTripleSeed_physical_coverage {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (t : Fin 3 → Fin m × Fin n) :
    ∃ a : Fin 10, ∃ σ : Equiv.Perm (Fin 3), ∃ ρ : Equiv.Perm (Fin m),
      ∃ κ : Equiv.Perm (Fin n), ∀ i,
        Prod.map ρ κ (t (σ i)) = finiteTriplePhysicalSeed hm hn a i := by
  classical
  obtain ⟨r,hr⟩ := threeTuplePatterns_complete _ (tupleFirstIndex_isPattern (fun i => (t i).1))
  obtain ⟨c,hc⟩ := threeTuplePatterns_complete _ (tupleFirstIndex_isPattern (fun i => (t i).2))
  obtain ⟨a,q,hqr,hqc⟩ := finiteTripleSeed_pattern_coverage r c
  let σ := Equiv.ofBijective (finiteTripleOrder q) (finiteTripleOrder_bijective q)
  have hrow (i j : Fin 3) : (t (σ i)).1 = (t (σ j)).1 ↔
      (finiteTriplePhysicalSeed hm hn a i).1 = (finiteTriplePhysicalSeed hm hn a j).1 := by
    have hp := (tupleFirstIndex_eq_iff (fun i => (t i).1) (σ i) (σ j)).symm
    rw [←hr] at hp
    exact hp.trans ((hqr i j).trans (by simp [finiteTriplePhysicalSeed]))
  have hcol (i j : Fin 3) : (t (σ i)).2 = (t (σ j)).2 ↔
      (finiteTriplePhysicalSeed hm hn a i).2 = (finiteTriplePhysicalSeed hm hn a j).2 := by
    have hp := (tupleFirstIndex_eq_iff (fun i => (t i).2) (σ i) (σ j)).symm
    rw [←hc] at hp
    exact hp.trans ((hqc i j).trans (by simp [finiteTriplePhysicalSeed]))
  obtain ⟨ρ,hρ⟩ := tupleHostPermutation (fun i => (t (σ i)).1)
    (fun i => (finiteTriplePhysicalSeed hm hn a i).1) hrow
  obtain ⟨κ,hκ⟩ := tupleHostPermutation (fun i => (t (σ i)).2)
    (fun i => (finiteTriplePhysicalSeed hm hn a i).2) hcol
  exact ⟨a,σ,ρ,κ,fun i => Prod.ext (hρ i) (hκ i)⟩

end DittertRybin.Certificates
