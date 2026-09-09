import DR.Rectangular.FourRowFiniteOrdinaryKernel
import DR.Certificates.PairNormalization
import Mathlib.Logic.Equiv.Sum

/-!
# Literal pair relations for two ordinary axes

The physical matrix distinguishes labelled rows and columns from interchangeable
ordinary ones. An ordinary pair records equality, not a chosen representative.
All averages and standard sectors below are formula-defined from that matrix
kernel, including ordinary multiplicity one. No seed or positivity is assumed.
-/

namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section

/-- The five possible kinds of a pair of distinguished/ordinary labels. -/
inductive OrdinaryPair (α : Type*)
  | dist (i j : α)
  | toOrdinary (i : α)
  | fromOrdinary (j : α)
  | same
  | different
  deriving DecidableEq

def OrdinaryPair.swap {α : Type*} : OrdinaryPair α → OrdinaryPair α
  | .dist i j => .dist j i
  | .toOrdinary i => .fromOrdinary i
  | .fromOrdinary j => .toOrdinary j
  | .same => .same
  | .different => .different

@[simp] theorem OrdinaryPair.swap_swap {α : Type*} (p : OrdinaryPair α) :
    p.swap.swap = p := by cases p <;> rfl

def ordinaryPair {α ρ : Type*} [DecidableEq ρ] : (α ⊕ ρ) → (α ⊕ ρ) → OrdinaryPair α
  | .inl i, .inl j => .dist i j
  | .inl i, .inr _ => .toOrdinary i
  | .inr _, .inl j => .fromOrdinary j
  | .inr r, .inr s => if r = s then .same else .different

theorem ordinaryPair_swap {α ρ : Type*} [DecidableEq ρ] (p q : α ⊕ ρ) :
    ordinaryPair q p = (ordinaryPair p q).swap := by
  cases p with
  | inl i => cases q <;> rfl
  | inr r =>
    cases q with
    | inl j => rfl
    | inr s =>
      by_cases h : r = s
      · simp [ordinaryPair, h, OrdinaryPair.swap]
      · simp [ordinaryPair, h, Ne.symm h, OrdinaryPair.swap]

/-- Averaging an ordinary pair uses the actual equal/unequal multiplicities. -/
def ordinaryPairAverage {α : Type*} (ell : ℝ) (f : OrdinaryPair α → ℝ) :
    Matrix (α ⊕ Unit) (α ⊕ Unit) ℝ
  | .inl i, .inl j => f (.dist i j)
  | .inl i, .inr _ => f (.toOrdinary i)
  | .inr _, .inl j => f (.fromOrdinary j)
  | .inr _, .inr _ => f .different + (f .same - f .different)/ell

theorem ordinaryPairAverage_ordinary {α : Type*} (ell : ℝ) (hell : ell ≠ 0)
    (f : OrdinaryPair α → ℝ) :
    ordinaryPairAverage ell f (.inr ()) (.inr ()) =
      (f .same + (ell-1)*f .different)/ell := by
  simp only [ordinaryPairAverage]
  field_simp
  ring

@[simp] theorem ordinaryPairAverage_one {α : Type*} (f : OrdinaryPair α → ℝ) :
    ordinaryPairAverage 1 f (.inr ()) (.inr ()) = f .same := by
  simp [ordinaryPairAverage]

variable {α β ρ γ : Type*}

def TwoAxisOrdinarySymm (K : OrdinaryPair α → OrdinaryPair β → ℝ) : Prop :=
  ∀ r c, K r.swap c.swap = K r c

def twoAxisOrdinaryMatrix [DecidableEq ρ] [DecidableEq γ]
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) :
    Matrix ((α ⊕ ρ) × (β ⊕ γ)) ((α ⊕ ρ) × (β ⊕ γ)) ℝ :=
  fun p q => K (ordinaryPair p.1 q.1) (ordinaryPair p.2 q.2)

theorem twoAxisOrdinaryMatrix_isSymm [DecidableEq ρ] [DecidableEq γ]
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (hK : TwoAxisOrdinarySymm K) :
    (twoAxisOrdinaryMatrix (ρ := ρ) (γ := γ) K).IsSymm := by
  apply Matrix.IsSymm.ext
  intro p q
  change K (ordinaryPair q.1 p.1) (ordinaryPair q.2 p.2) =
    K (ordinaryPair p.1 q.1) (ordinaryPair p.2 q.2)
  rw [ordinaryPair_swap p.1 q.1, ordinaryPair_swap p.2 q.2]
  exact hK _ _

def twoAxisTrivialMatrix (K : OrdinaryPair α → OrdinaryPair β → ℝ) (R C : ℝ) :
    Matrix ((α ⊕ Unit) × (β ⊕ Unit)) ((α ⊕ Unit) × (β ⊕ Unit)) ℝ :=
  fun p q => ordinaryPairAverage R
    (fun r => ordinaryPairAverage C (K r) p.2 q.2) p.1 q.1

def twoAxisRowStandardMatrix (K : OrdinaryPair α → OrdinaryPair β → ℝ) (C : ℝ) :
    Matrix (β ⊕ Unit) (β ⊕ Unit) ℝ :=
  ordinaryPairAverage C (fun c => K .same c - K .different c)

def twoAxisColumnStandardMatrix (K : OrdinaryPair α → OrdinaryPair β → ℝ) (R : ℝ) :
    Matrix (α ⊕ Unit) (α ⊕ Unit) ℝ :=
  ordinaryPairAverage R (fun r => K r .same - K r .different)

def twoAxisInteraction (K : OrdinaryPair α → OrdinaryPair β → ℝ) : ℝ :=
  K .same .same - K .different .same - K .same .different + K .different .different

def ordinaryAxisWeight (R : ℝ) : (α ⊕ Unit) → ℝ
  | .inl _ => 1
  | .inr _ => R

def twoAxisAggregateWeight (R C : ℝ) (p : (α ⊕ Unit) × (β ⊕ Unit)) : ℝ :=
  ordinaryAxisWeight R p.1 * ordinaryAxisWeight C p.2

theorem twoAxisTrivialMatrix_averages_commute
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (R C : ℝ)
    (p q : (α ⊕ Unit) × (β ⊕ Unit)) :
    twoAxisTrivialMatrix K R C p q = ordinaryPairAverage C
      (fun c => ordinaryPairAverage R (fun r => K r c) p.1 q.1) p.2 q.2 := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [twoAxisTrivialMatrix, ordinaryPairAverage]
  all_goals ring

/-- Group physical rows without changing either row or within-row coordinates. -/
def ordinaryAxisEquiv (α ρ β : Type*) : ((α ⊕ ρ) × β) ≃ ((α × β) ⊕ (ρ × β)) :=
  Equiv.sumProdDistrib α ρ β

def ordinaryCompressedEquiv (α β : Type*) :
    ((α ⊕ Unit) × β) ≃ ((α × β) ⊕ β) where
  toFun p := match p.1 with
    | .inl i => .inl (i,p.2)
    | .inr _ => .inr p.2
  invFun q := match q with
    | .inl p => (.inl p.1,p.2)
    | .inr j => (.inr (),j)
  left_inv p := by rcases p with ⟨i,j⟩; cases i <;> rfl
  right_inv q := by cases q <;> rfl

/-- A matrix family indexed by one ordinary-axis pair, before averaging. -/
def ordinaryPairMatrix [DecidableEq ρ] (K : OrdinaryPair α → Matrix β β ℝ) :
    Matrix ((α ⊕ ρ) × β) ((α ⊕ ρ) × β) ℝ :=
  fun p q => K (ordinaryPair p.1 q.1) p.2 q.2

def ordinaryPairAggregate (K : OrdinaryPair α → Matrix β β ℝ) (R : ℝ) :
    Matrix ((α ⊕ Unit) × β) ((α ⊕ Unit) × β) ℝ :=
  fun p q => ordinaryPairAverage R (fun r => K r p.2 q.2) p.1 q.1

def OrdinaryPairMatrixSymm (K : OrdinaryPair α → Matrix β β ℝ) : Prop :=
  ∀ r i j, K r.swap j i = K r i j

def ordinaryPairDistinguished (K : OrdinaryPair α → Matrix β β ℝ) :
    Matrix (α × β) (α × β) ℝ := fun p q => K (.dist p.1 q.1) p.2 q.2

def ordinaryPairCross (K : OrdinaryPair α → Matrix β β ℝ) :
    Matrix (α × β) β ℝ := fun p j => K (.toOrdinary p.1) p.2 j

theorem ordinaryPairMatrix_reindex [DecidableEq ρ]
    (K : OrdinaryPair α → Matrix β β ℝ) (hK : OrdinaryPairMatrixSymm K) :
    ordinaryPairMatrix (ρ := ρ) K =
      (ordinaryColumnMatrix (ordinaryPairDistinguished K) (ordinaryPairCross K)
        (K .same) (K .different)).submatrix (ordinaryAxisEquiv α ρ β) (ordinaryAxisEquiv α ρ β) := by
  ext p q
  rcases p with ⟨i,a⟩
  rcases q with ⟨j,b⟩
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases j with
    | inl j =>
      change K (.fromOrdinary j) a b = K (.toOrdinary j) b a
      exact (hK (.fromOrdinary j) a b).symm
    | inr j =>
      by_cases h : i = j <;>
        simp [ordinaryPairMatrix, ordinaryPair, Matrix.submatrix, ordinaryAxisEquiv,
          Equiv.sumProdDistrib, ordinaryColumnMatrix, h]

theorem ordinaryPairAggregate_reindex
    (K : OrdinaryPair α → Matrix β β ℝ) (hK : OrdinaryPairMatrixSymm K) (R : ℝ) :
    ordinaryPairAggregate K R =
      (ordinaryAggregateMatrix (ordinaryPairDistinguished K) (ordinaryPairCross K)
        (K .same) (K .different) R).submatrix
        (ordinaryCompressedEquiv α β) (ordinaryCompressedEquiv α β) := by
  ext p q
  rcases p with ⟨i,a⟩
  rcases q with ⟨j,b⟩
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases j with
    | inl j =>
      change K (.fromOrdinary j) a b = K (.toOrdinary j) b a
      exact (hK (.fromOrdinary j) a b).symm
    | inr j => rfl

def ordinaryPairAggregateVector [Fintype ρ]
    (p : (α ⊕ ρ) × β → ℝ) : (α ⊕ Unit) × β → ℝ
  | (.inl i,j) => p (.inl i,j)
  | (.inr _,j) => ∑ r, p (.inr r,j)

def ordinaryPairFluctuation [Fintype ρ]
    (p : (α ⊕ ρ) × β → ℝ) (r : ρ) (j : β) : ℝ :=
  p (.inr r,j) - (∑ s, p (.inr s,j))/(Fintype.card ρ : ℝ)

/-- The one-axis identity on the literal product index, with exact sum coordinates. -/
theorem quadraticValue_ordinaryPair_decomposition
    [Fintype α] [Fintype β] [Fintype ρ] [DecidableEq ρ]
    (K : OrdinaryPair α → Matrix β β ℝ) (hK : OrdinaryPairMatrixSymm K)
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (p : (α ⊕ ρ) × β → ℝ) :
    quadraticValue (ordinaryPairMatrix K) p =
      quadraticValue (ordinaryPairAggregate K (Fintype.card ρ))
        (ordinaryPairAggregateVector p) +
      ∑ r, quadraticValue (K .same - K .different) (ordinaryPairFluctuation p r) := by
  classical
  rw [ordinaryPairMatrix_reindex K hK, ordinaryPairAggregate_reindex K hK,
    quadraticValue_submatrix_equiv, quadraticValue_submatrix_equiv]
  have hp : (fun i => p ((ordinaryAxisEquiv α ρ β).symm i)) =
      Sum.elim (fun q : α × β => p (.inl q.1,q.2))
        (fun q : ρ × β => p (.inr q.1,q.2)) := by
    funext i
    cases i <;> rfl
  have hz : (fun i => ordinaryPairAggregateVector p ((ordinaryCompressedEquiv α β).symm i)) =
      Sum.elim (fun q : α × β => p (.inl q.1,q.2))
        (fun j : β => ∑ r, p (.inr r,j)) := by
    funext i
    cases i <;> rfl
  rw [hp,hz]
  exact quadraticValue_ordinaryColumn_decomposition (ordinaryPairDistinguished K)
    (ordinaryPairCross K) (K .same) (K .different)
    (fun q : α × β => p (.inl q.1,q.2)) (fun r j => p (.inr r,j)) hR

end
end DittertRybin.Certificates
