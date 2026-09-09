import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-! A small exact sparse arithmetic evaluator with a proved interpretation.

The data operations use only lists, natural exponents and rational arithmetic.
Their equations are checked by ordinary kernel reduction; soundness is proved
for every rational algebra. No native evaluator is trusted.
-/
namespace DittertRybin.Certificates.SparsePolynomial
noncomputable section
open scoped BigOperators

abbrev Exponent := ℕ × ℕ × ℕ
abbrev Term := Exponent × ℚ
abbrev Polynomial := List Term

def exponentAdd (a b : Exponent) : Exponent := (a.1+b.1, a.2.1+b.2.1, a.2.2+b.2.2)

def exponentBefore (a b : Exponent) : Prop :=
  a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧
    (a.2.2 < b.2.2 ∨ (a.2.2 = b.2.2 ∧ a.1 < b.1)))

instance (a b : Exponent) : Decidable (exponentBefore a b) := by
  unfold exponentBefore
  infer_instance

def insert (t : Term) : Polynomial → Polynomial
  | [] => if t.2 = 0 then [] else [t]
  | u :: p => if t.2 = 0 then u :: p else
      if t.1 = u.1 then
        if t.2 + u.2 = 0 then p else (t.1, t.2+u.2) :: p
      else if exponentBefore t.1 u.1 then t :: u :: p else u :: insert t p

def mergeAux : ℕ → Polynomial → Polynomial → Polynomial
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, t::p, u::q =>
    if t.1 = u.1 then
      if t.2 + u.2 = 0 then mergeAux n p q
      else (t.1,t.2+u.2) :: mergeAux n p q
    else if exponentBefore t.1 u.1 then t :: mergeAux n p (u::q)
    else u :: mergeAux n (t::p) q

def removeZeros (p : Polynomial) : Polynomial := p.filter fun t => t.2 ≠ 0

/-- Merge normalized terms in linear list traversal, retaining a proved interpretation
for arbitrary inputs. Filtering removes zero terms supplied by dense tensors. -/
def add (p q : Polynomial) : Polynomial :=
  let p' := removeZeros p
  let q' := removeZeros q
  mergeAux (p'.length + q'.length) p' q'

def scaleTerm (t : Term) (p : Polynomial) : Polynomial :=
  p.map fun u => (exponentAdd t.1 u.1, t.2*u.2)

def mul (p q : Polynomial) : Polynomial :=
  p.foldr (fun t r => add (scaleTerm t q) r) []

def constant (c : ℚ) : Polynomial := if c = 0 then [] else [((0,0,0),c)]

def var (i : Fin 3) : Polynomial :=
  if i = 0 then [((1,0,0),1)] else if i = 1 then [((0,1,0),1)] else [((0,0,1),1)]

def pow (p : Polynomial) : ℕ → Polynomial
  | 0 => constant 1
  | n+1 => mul p (pow p n)

def neg (p : Polynomial) : Polynomial := mul (constant (-1)) p

def sub (p q : Polynomial) : Polynomial := add p (neg q)

def monomial {R : Type*} [CommRing R] (x : Fin 3 → R) (e : Exponent) : R :=
  x 0 ^ e.1 * x 1 ^ e.2.1 * x 2 ^ e.2.2

def termValue {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 3 → R) (t : Term) : R :=
  algebraMap ℚ R t.2 * monomial x t.1

def value {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 3 → R) (p : Polynomial) : R :=
  (p.map (termValue x)).sum

theorem value_insert {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (t : Term) (p : Polynomial) :
    value x (insert t p) = termValue x t + value x p := by
  induction p with
  | nil =>
      by_cases hz : t.2 = 0
      · simp [insert, hz, value, termValue]
      · simp [insert, hz, value]
  | cons u p ih =>
      by_cases hz : t.2 = 0
      · simp [insert, hz, value, termValue]
      · by_cases he : t.1 = u.1
        · by_cases hs : t.2+u.2 = 0
          · have hcast := congrArg (algebraMap ℚ R) hs
            simp only [map_add, map_zero] at hcast
            simp only [insert, hz, he, hs, if_true, if_false, value,
              List.map_cons, List.sum_cons]
            simp only [termValue, he]
            rw [← add_assoc, ← add_mul, hcast, zero_mul, zero_add]
          · simp only [insert, hz, he, hs, if_true, if_false, value,
              List.map_cons, List.sum_cons, termValue, map_add]
            ring
        · by_cases hb : exponentBefore t.1 u.1
          · simp [insert, hz, he, hb, value]
          · simp only [insert, hz, he, hb, if_false]
            change termValue x u + value x (insert t p) = _
            rw [ih]
            simp [value, add_left_comm]

theorem value_mergeAux {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (n : ℕ) (p q : Polynomial) :
    value x (mergeAux n p q) = value x p + value x q := by
  induction n generalizing p q with
  | zero => simp [mergeAux, value]
  | succ n ih =>
    cases p with
    | nil => simp [mergeAux, value]
    | cons t p =>
      cases q with
      | nil => simp [mergeAux, value]
      | cons u q =>
        by_cases he : t.1 = u.1
        · by_cases hz : t.2+u.2 = 0
          · have hc := congrArg (algebraMap ℚ R) hz
            simp only [map_add, map_zero] at hc
            simp only [mergeAux, he, hz, if_true, ih]
            simp only [value, List.map_cons, List.sum_cons, termValue, he]
            linear_combination -monomial x u.1 * hc
          · simp only [mergeAux, he, hz, if_true, if_false]
            change termValue x (u.1,t.2+u.2) + value x (mergeAux n p q) = _
            rw [ih]
            simp only [value, List.map_cons, List.sum_cons, termValue, he, map_add]
            ring
        · by_cases hb : exponentBefore t.1 u.1
          · simp only [mergeAux, he, hb, if_true, if_false]
            change termValue x t + value x (mergeAux n p (u::q)) = _
            rw [ih]
            simp [value, add_assoc]
          · simp only [mergeAux, he, hb, if_false]
            change termValue x u + value x (mergeAux n (t::p) q) = _
            rw [ih]
            simp only [value, List.map_cons, List.sum_cons]
            ring


theorem value_removeZeros {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (p : Polynomial) : value x (removeZeros p) = value x p := by
  induction p with
  | nil => simp [removeZeros, value]
  | cons t p ih =>
    by_cases ht : t.2 = 0
    · simpa [removeZeros, ht, value, termValue] using ih
    · simpa [removeZeros, ht, value] using congrArg (termValue x t + ·) ih
theorem value_add {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (p q : Polynomial) : value x (add p q) = value x p + value x q := by
  simp only [add, value_mergeAux, value_removeZeros]

theorem monomial_add {R : Type*} [CommRing R] (x : Fin 3 → R) (a b : Exponent) :
    monomial x (exponentAdd a b) = monomial x a * monomial x b := by
  simp only [monomial, exponentAdd, pow_add]
  ring

theorem value_scaleTerm {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (t : Term) (p : Polynomial) :
    value x (scaleTerm t p) = termValue x t * value x p := by
  induction p with
  | nil => simp [scaleTerm, value]
  | cons u p ih =>
      simp only [scaleTerm, List.map_cons]
      change termValue x (exponentAdd t.1 u.1,t.2*u.2) + value x (scaleTerm t p) = _
      rw [ih]
      simp only [value, List.map_cons, List.sum_cons, termValue, map_mul, monomial_add]
      ring

theorem value_mul {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (p q : Polynomial) : value x (mul p q) = value x p * value x q := by
  induction p with
  | nil => simp [mul, value]
  | cons t p ih =>
      simp only [mul, List.foldr_cons, value_add]
      rw [← mul, ih, value_scaleTerm]
      simp [value, add_mul]

theorem value_constant {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (c : ℚ) : value x (constant c) = algebraMap ℚ R c := by
  by_cases hz : c = 0 <;> simp [constant, hz, value, termValue, monomial]

theorem value_variable {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (i : Fin 3) : value x (var i) = x i := by
  rcases i with ⟨i,hi⟩
  interval_cases i <;> simp [var, value, termValue, monomial]

theorem value_pow {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (p : Polynomial) (n : ℕ) : value x (pow p n) = value x p ^ n := by
  induction n with
  | zero => simp [pow, value_constant]
  | succ n ih => rw [pow, value_mul, ih, pow_succ']

theorem value_neg {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (p : Polynomial) : value x (neg p) = - value x p := by
  simp [neg, value_mul, value_constant]

theorem value_sub {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : Fin 3 → R) (p q : Polynomial) : value x (sub p q) = value x p - value x q := by
  simp [sub, value_add, value_neg, sub_eq_add_neg]

end
end DittertRybin.Certificates.SparsePolynomial
