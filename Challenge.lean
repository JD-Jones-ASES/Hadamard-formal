import Mathlib

/-!
# Hadamard formalization challenge

The public challenge asks for a parity obstruction, the periodic
Cooper--Wallis construction, and eight concrete Hadamard existence results.
The challenge deliberately imports only Mathlib; the proof holes below are the
problem to be solved.
-/

namespace HadamardFormal

open scoped BigOperators

/-- An integer is a Hadamard sign when it is `+1` or `-1`. -/
def IsSign (z : ℤ) : Prop :=
  z = 1 ∨ z = -1

/-- An integer sequence indexed by the cyclic group `Fin n`. -/
abbrev Sequence (n : ℕ) := Fin n → ℤ

/-- Four integer sequences of a common order. -/
abbrev Quadruple (n : ℕ) := Fin 4 → Sequence n

/-- Periodic autocorrelation, `PAF(x)(s) = sum_q x[q] x[q+s]`. -/
def paf {n : ℕ} [NeZero n] (x : Sequence n) (s : Fin n) : ℤ :=
  ∑ q, x q * x (q + s)

/-- The integer delta function at zero on `Fin n`. -/
def deltaZero {n : ℕ} [NeZero n] (s : Fin n) : ℤ :=
  if s = 0 then 1 else 0

/-- The alphabet for a T-matrix entry. -/
def IsTEntry (z : ℤ) : Prop :=
  z = 0 ∨ IsSign z

/-- The number of nonzero components at one position of a quadruple. -/
def supportCount {n : ℕ} (T : Quadruple n) (q : Fin n) : ℕ :=
  (Finset.univ.filter fun i ↦ T i q ≠ 0).card

/-- A periodic T-matrix quadruple of order `n`. -/
def IsTMatrixQuadruple {n : ℕ} [NeZero n] (T : Quadruple n) : Prop :=
  (∀ i q, IsTEntry (T i q)) ∧
    (∀ q, supportCount T q = 1) ∧
      ∀ s, ∑ i, paf (T i) s = (n : ℤ) * deltaZero s

/-- A cyclic sequence is symmetric when reversing its index fixes it. -/
def IsSymmetricSequence {n : ℕ} [NeZero n] (x : Sequence n) : Prop :=
  ∀ q, x (-q) = x q

/-- A symmetric-circulant Williamson quadruple of order `n`. -/
def IsWilliamson {n : ℕ} [NeZero n] (W : Quadruple n) : Prop :=
  (∀ i q, IsSign (W i q)) ∧
    (∀ i, IsSymmetricSequence (W i)) ∧
      ∀ s, ∑ i, paf (W i) s = 4 * (n : ℤ) * deltaZero s

/-- There exists a classical integer Hadamard matrix of order `n`. -/
def HadamardExists (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard

/-- A symmetric sign matrix with zero diagonal and zero row sums has order
congruent to one modulo four. -/
theorem handshake_mod_four
    (m : ℕ)
    (hm : Odd m)
    (D : Matrix (Fin m) (Fin m) ℤ)
    (hsymm : D.transpose = D)
    (hdiag : ∀ i, D i i = 0)
    (hoff : ∀ i j, i ≠ j → D i j = 1 ∨ D i j = -1)
    (hrow : ∀ i, ∑ j, D i j = 0) :
    m % 4 = 1 := by
  sorry

/-- Cooper--Wallis existence theorem for periodic T-matrix and Williamson
quadruples. -/
theorem cooperWallis {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) :
    HadamardExists (4 * t * w) := by
  sorry

/-- A Hadamard matrix of order `7172 = 4 · 163 · 11` exists. -/
theorem hadamard_7172 : HadamardExists 7172 := by
  sorry

/-- A Hadamard matrix of order `8476 = 4 · 163 · 13` exists. -/
theorem hadamard_8476 : HadamardExists 8476 := by
  sorry

/-- A Hadamard matrix of order `2884 = 4 · 103 · 7` exists. -/
theorem hadamard_2884 : HadamardExists 2884 := by
  sorry

/-- A Hadamard matrix of order `4532 = 4 · 103 · 11` exists. -/
theorem hadamard_4532 : HadamardExists 4532 := by
  sorry

/-- A Hadamard matrix of order `7004 = 4 · 103 · 17` exists. -/
theorem hadamard_7004 : HadamardExists 7004 := by
  sorry

/-- A Hadamard matrix of order `7828 = 4 · 103 · 19` exists. -/
theorem hadamard_7828 : HadamardExists 7828 := by
  sorry

/-- A Hadamard matrix of order `9476 = 4 · 103 · 23` exists. -/
theorem hadamard_9476 : HadamardExists 9476 := by
  sorry

/-- A Hadamard matrix of order `11948 = 4 · 103 · 29` exists. -/
theorem hadamard_11948 : HadamardExists 11948 := by
  sorry

end HadamardFormal
