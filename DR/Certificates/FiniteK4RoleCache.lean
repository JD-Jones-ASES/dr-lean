import DR.Certificates.FiniteK4RoleSemantics
import DR.Certificates.FiniteK4AxisData

/-! Share the 624 one-axis normalizations across the 2704 physical pattern
pairs. The cache is proved equal to the actual first-occurrence formula. -/

namespace DittertRybin.Certificates
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem finiteK4PositionOrders_correct : List.ofFn finiteK4PositionOrders =
    ([0,1,2] : List (Fin 5)).permutations'.flatMap (fun p =>
      ([3,4] : List (Fin 5)).permutations'.map (fun q => p ++ q)) := by
  decide +kernel

theorem finiteK4TupleRoleKey_orderFold (s : Fin 5 → ℕ × ℕ) :
    finiteK4TupleRoleKey s = (List.ofFn (fun o =>
      fourRowFiniteNormalizedKey ((finiteK4PositionOrders o).map s))).foldl min (25^5) := by
  have he : List.ofFn (fun o => fourRowFiniteNormalizedKey ((finiteK4PositionOrders o).map s)) =
      (List.ofFn finiteK4PositionOrders).map (fun p => fourRowFiniteNormalizedKey (p.map s)) := by
    rw [List.map_ofFn]
    rfl
  rw [he, finiteK4PositionOrders_correct]
  change fourRowFiniteCanonicalRoleKey (([0,1,2] : List (Fin 5)).map s) (s 3) (s 4) = _
  unfold fourRowFiniteCanonicalRoleKey
  change (((([0,1,2] : List (Fin 5)).map s).permutations'.flatMap
    (fun p => (([3,4] : List (Fin 5)).map s).permutations'.map
      (fun q => fourRowFiniteNormalizedKey (p ++ q)))).foldl min (25^5)) = _
  simp only [← List.map_permutations', List.flatMap_map, List.map_flatMap,
    List.map_map, List.map_append, Function.comp_def]

theorem finiteK4AxisLabels_correct : ∀ r : Fin 52, ∀ o : Fin 12,
    firstOccurrenceLabels ((finiteK4PositionOrders o).map
      (fun i => (fiveTuplePatterns r i).val)) = (finiteK4AxisLabels.get r).get o := by
  decide +kernel

def finiteK4CachedNormalizedKey (r c : Fin 52) (o : Fin 12) : ℕ :=
  (((finiteK4AxisLabels.get r).get o).zip ((finiteK4AxisLabels.get c).get o)).foldl
    (fun z p => 25*z + 5*p.1 + p.2) 0

def finiteK4CachedRoleKey (r c : Fin 52) : ℕ :=
  (List.ofFn (finiteK4CachedNormalizedKey r c)).foldl min (25^5)

theorem finiteK4TupleRoleKey_pattern_cache (r c : Fin 52) :
    finiteK4TupleRoleKey (finiteK4PatternCell r c) = finiteK4CachedRoleKey r c := by
  rw [finiteK4TupleRoleKey_orderFold]
  unfold finiteK4CachedRoleKey
  congr 1
  apply congrArg List.ofFn
  funext o
  unfold fourRowFiniteNormalizedKey finiteK4CachedNormalizedKey
  simp only [List.map_map, Function.comp_def, finiteK4PatternCell,
    finiteK4AxisLabels_correct]

end
end DittertRybin.Certificates
