import DR.Certificates.FiniteK3QuarticData
import Mathlib.Algebra.BigOperators.Fin

/-!
# The literal quartic equations and six-pair symmetrization

Every ordered quartet can be averaged over its six choices of a multiplier
pair. Repeated multiplier cells receive coefficient two before dividing by
twelve. These integer relations connect the source's 33 unordered-monomial
equations to all 225 row/column equality patterns.
-/

namespace DittertRybin.Certificates
open scoped BigOperators

def finiteK3PairOrder : Fin 6 → (Fin 4 → Fin 4) :=
  ![![0,1,2,3], ![0,2,1,3], ![0,3,1,2],
    ![1,2,0,3], ![1,3,0,2], ![2,3,0,1]]

theorem finiteK3PairOrder_bijective : ∀ q : Fin 6, Function.Bijective (finiteK3PairOrder q) := by
  decide +kernel

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def finiteK3MultiplierWeight (r : Fin 4 → α) (c : Fin 4 → β) : Nat :=
  if r 0 = r 1 ∧ c 0 = c 1 then 2 else 1

/-- Literal inclusive-OR success on the three retained sample positions. -/
def finiteK3DeletedSuccess (r : Fin 4 → α) (c : Fin 4 → β) (a : Fin 4) : Nat :=
  if Function.Injective (r ∘ a.succAbove) ∨ Function.Injective (c ∘ a.succAbove) then 1 else 0

def finiteK3PatternPairCoefficient (r c : Fin 15) (k : Fin 93) : Nat :=
  ∑ q : Fin 6,
    if finiteK3Role (fourTuplePatterns r ∘ finiteK3PairOrder q)
        (fourTuplePatterns c ∘ finiteK3PairOrder q) = k then
      finiteK3MultiplierWeight (fourTuplePatterns r ∘ finiteK3PairOrder q)
        (fourTuplePatterns c ∘ finiteK3PairOrder q) else 0

def finiteK3PatternEquation (r c : Fin 15) : Fin 33 :=
  (finiteK3QuarticPatternEquation.get r).get c

def finiteK3PatternPairIndex (r c : Fin 15) : Fin 225 := ⟨15*r.val+c.val, by omega⟩

def finiteK3PatternPairRole (r c : Fin 15) (q : Fin 6) : Fin 93 :=
  (finiteK3QuarticPairRoles.get (finiteK3PatternPairIndex r c)).get q

def finiteK3PatternPairWeight (r c : Fin 15) (q : Fin 6) : Nat :=
  (finiteK3QuarticPairWeights.get (finiteK3PatternPairIndex r c)).get q

def finiteK3TablePairCoefficient (r c : Fin 15) (k : Fin 93) : Nat :=
  ∑ q : Fin 6, if finiteK3PatternPairRole r c q = k then finiteK3PatternPairWeight r c q else 0

def finiteK3PairPattern (r : Fin 15) (q : Fin 6) : Fin 15 :=
  (finiteK3QuarticPairPatterns.get r).get q

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PairPattern_compression : ∀ r : Fin 15, ∀ q : Fin 6,
    tupleFirstIndex (fourTuplePatterns r ∘ finiteK3PairOrder q) =
      fourTuplePatterns (finiteK3PairPattern r q) := by
  decide +kernel

theorem finiteK3PairPattern_index (r : Fin 15) (q : Fin 6) :
    fourTuplePatternIndex (fourTuplePatterns r ∘ finiteK3PairOrder q) =
      finiteK3PairPattern r q := by
  apply fourTuplePatterns_injective
  rw [fourTuplePatternIndex_spec, finiteK3PairPattern_compression]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteK3PatternPairTableData : ∀ r c : Fin 15, ∀ q : Fin 6,
    finiteK3TableRole (finiteK3PairPattern r q) (finiteK3PairPattern c q) =
      finiteK3PatternPairRole r c q ∧
    finiteK3MultiplierWeight (fourTuplePatterns r ∘ finiteK3PairOrder q)
      (fourTuplePatterns c ∘ finiteK3PairOrder q) = finiteK3PatternPairWeight r c q := by
  decide +kernel

theorem finiteK3PatternPairData : ∀ r c : Fin 15, ∀ q : Fin 6,
    finiteK3Role (fourTuplePatterns r ∘ finiteK3PairOrder q)
      (fourTuplePatterns c ∘ finiteK3PairOrder q) = finiteK3PatternPairRole r c q ∧
    finiteK3MultiplierWeight (fourTuplePatterns r ∘ finiteK3PairOrder q)
      (fourTuplePatterns c ∘ finiteK3PairOrder q) = finiteK3PatternPairWeight r c q := by
  simp only [finiteK3Role, finiteK3PairPattern_index]
  exact finiteK3PatternPairTableData

theorem finiteK3PatternPairCoefficient_eq_table (r c : Fin 15) (k : Fin 93) :
    finiteK3PatternPairCoefficient r c k = finiteK3TablePairCoefficient r c k := by
  unfold finiteK3PatternPairCoefficient finiteK3TablePairCoefficient
  simp_rw [(finiteK3PatternPairData r c _).1, (finiteK3PatternPairData r c _).2]

theorem finiteK3QuarticMultiplicity_pos : ∀ a : Fin 33, 0 < finiteK3QuarticMultiplicity.get a := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check00 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 0 c) *
      finiteK3TablePairCoefficient 0 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 0 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check01 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 1 c) *
      finiteK3TablePairCoefficient 1 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 1 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check02 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 2 c) *
      finiteK3TablePairCoefficient 2 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 2 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check03 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 3 c) *
      finiteK3TablePairCoefficient 3 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 3 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check04 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 4 c) *
      finiteK3TablePairCoefficient 4 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 4 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check05 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 5 c) *
      finiteK3TablePairCoefficient 5 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 5 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check06 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 6 c) *
      finiteK3TablePairCoefficient 6 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 6 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check07 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 7 c) *
      finiteK3TablePairCoefficient 7 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 7 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check08 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 8 c) *
      finiteK3TablePairCoefficient 8 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 8 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check09 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 9 c) *
      finiteK3TablePairCoefficient 9 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 9 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check10 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 10 c) *
      finiteK3TablePairCoefficient 10 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 10 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check11 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 11 c) *
      finiteK3TablePairCoefficient 11 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 11 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check12 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 12 c) *
      finiteK3TablePairCoefficient 12 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 12 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check13 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 13 c) *
      finiteK3TablePairCoefficient 13 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 13 c)).get k) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_check14 : ∀ c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 14 c) *
      finiteK3TablePairCoefficient 14 c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation 14 c)).get k) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem finiteK3PatternPairCoefficient_identity : ∀ r c : Fin 15, ∀ k : Fin 93,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation r c) *
      finiteK3PatternPairCoefficient r c k =
        12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation r c)).get k) := by
  have htable : ∀ r c : Fin 15, ∀ k : Fin 93,
      finiteK3QuarticMultiplicity.get (finiteK3PatternEquation r c) *
        finiteK3TablePairCoefficient r c k =
          12 * ((finiteK3QuarticRows.get (finiteK3PatternEquation r c)).get k) := by
    intro r
    fin_cases r
    · exact finiteK3PatternPairCoefficient_check00
    · exact finiteK3PatternPairCoefficient_check01
    · exact finiteK3PatternPairCoefficient_check02
    · exact finiteK3PatternPairCoefficient_check03
    · exact finiteK3PatternPairCoefficient_check04
    · exact finiteK3PatternPairCoefficient_check05
    · exact finiteK3PatternPairCoefficient_check06
    · exact finiteK3PatternPairCoefficient_check07
    · exact finiteK3PatternPairCoefficient_check08
    · exact finiteK3PatternPairCoefficient_check09
    · exact finiteK3PatternPairCoefficient_check10
    · exact finiteK3PatternPairCoefficient_check11
    · exact finiteK3PatternPairCoefficient_check12
    · exact finiteK3PatternPairCoefficient_check13
    · exact finiteK3PatternPairCoefficient_check14
  intro r c k
  rw [finiteK3PatternPairCoefficient_eq_table]
  exact htable r c k

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3PatternDeletedSuccess_identity : ∀ r c : Fin 15,
    finiteK3QuarticMultiplicity.get (finiteK3PatternEquation r c) * 3 *
      (∑ a, finiteK3DeletedSuccess (fourTuplePatterns r) (fourTuplePatterns c) a) =
        12 * finiteK3QuarticSuccesses.get (finiteK3PatternEquation r c) := by
  decide +kernel

end DittertRybin.Certificates
