import Mathlib

/-!
# Hadamard formalization challenge

The public challenge asks for the handshake parity obstruction and its
empty-class corollary — the mathematical core of an erratum to Miyamoto's
1991 construction paper — the generic periodic Cooper--Wallis construction,
and Hadamard existence at eight orders, each listed as not recorded known in
Table 4 of the Cati--Pasechnik construction database (arXiv:2411.18897v2,
2025-08-30). The challenge deliberately imports only Mathlib; the proof
holes below are the problem to be solved.
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

/-- A symmetric integer matrix of odd order with zero diagonal, off-diagonal
entries in `{+1, -1}`, and zero row sums has order congruent to one modulo
four.  This is the parity obstruction behind the erratum to Miyamoto 1991
(J. Combin. Theory Ser. A 57, 86--108): any instance of that paper's
Corollary 4 forces such a matrix at the corollary's block order. -/
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

/-- For a positive order `m` with `m % 4 ≠ 1` the class above is empty.
For odd orders this is the contrapositive of the obstruction; for even
orders each row carries an odd number of `±1` entries, which cannot sum to
zero.  The concrete erratum application is `no_c2_matrix` below. -/
theorem no_handshake_matrix (m : ℕ) (hm0 : 0 < m) (hm : m % 4 ≠ 1) :
    ¬ ∃ D : Matrix (Fin m) (Fin m) ℤ,
        D.transpose = D ∧ (∀ i, D i i = 0) ∧
          (∀ i j, i ≠ j → D i j = 1 ∨ D i j = -1) ∧ ∀ i, ∑ j, D i j = 0 := by
  sorry

/-- The displayed block form of the C₂-matrix consumed by Corollary 4 of
Miyamoto 1991: `[[0, e, 0, e], [eᵀ, D₁, eᵀ, D₂], [0, e, 0, -e],
[eᵀ, D₂, -eᵀ, -D₁]]`, with interior blocks `D₁, D₂` of order `m`. -/
def c2Display (m : ℕ) (D₁ D₂ : Matrix (Fin m) (Fin m) ℤ) :
    Matrix ((Fin 1 ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin m))
      ((Fin 1 ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin m)) ℤ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks 0 (Matrix.of fun _ _ ↦ 1) (Matrix.of fun _ _ ↦ 1) D₁)
    (Matrix.fromBlocks 0 (Matrix.of fun _ _ ↦ 1) (Matrix.of fun _ _ ↦ 1) D₂)
    (Matrix.fromBlocks 0 (Matrix.of fun _ _ ↦ 1) (Matrix.of fun _ _ ↦ 1) D₂)
    (Matrix.fromBlocks 0 (Matrix.of fun _ _ ↦ -1) (Matrix.of fun _ _ ↦ -1) (-D₁))

/-- The erratum's application: the C₂-matrix ingredient of Miyamoto 1991's
Corollary 4 has no instance at any positive block order `m` with
`m % 4 ≠ 1` — no symmetric interior pair `D₁, D₂` satisfying the pairing
condition of the paper's hypothesis (4.1) against the identity blocks makes
the displayed form satisfy `D * Dᵀ = 2m • 1`.  At `m = 51, 63, 75` this
covers the paper's printed list entries at orders `103`, `127` and `151`;
at `m = 50` it also closes the printed `4(2m + 3)` reading of the
corollary's output order.  The order-515 list entry fed by order `103`, the
paper's claim of a Hadamard matrix of order `2060`, is therefore
unsupported by the paper's own machinery.  Order 2060 itself is not open: a
Hadamard matrix of that order was posted publicly on 2026-08-23, credited
to Schneider, by other means — the erratum concerns the paper's route, not
the order's status.  The transcriptions of the displayed form, hypothesis
(4.1), and the section-7 lists, and the reading that Corollary 4 is the
paper's only engine at odd part `≡ 3 (mod 4)`, are the source note's
human-audited premises. -/
theorem no_c2_matrix (m : ℕ) (hm0 : 0 < m) (hm : m % 4 ≠ 1) :
    ¬ ∃ D₁ D₂ : Matrix (Fin m) (Fin m) ℤ,
        D₁.transpose = D₁ ∧ D₂.transpose = D₂ ∧
          (∀ i j, IsSign ((D₁ + 1) i j) ∧ IsSign ((D₁ - 1) i j)) ∧
            (∀ i j, IsSign ((D₂ + 1) i j) ∧ IsSign ((D₂ - 1) i j)) ∧
              c2Display m D₁ D₂ * (c2Display m D₁ D₂).transpose
                = (2 * (m : ℤ)) • 1 := by
  sorry

/-- Cooper--Wallis existence theorem for periodic T-matrix and Williamson
quadruples. -/
theorem cooperWallis {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) :
    HadamardExists (4 * t * w) := by
  sorry

/-- A Hadamard matrix of order `7172 = 4 · 163 · 11` exists.  Table 4 of
arXiv:2411.18897v2 carries the entry `1793(4)`: no such matrix recorded. -/
theorem hadamard_7172 : HadamardExists 7172 := by
  sorry

/-- A Hadamard matrix of order `8476 = 4 · 163 · 13` exists.  Table 4 of
arXiv:2411.18897v2 carries the entry `2119(4)`: no such matrix recorded. -/
theorem hadamard_8476 : HadamardExists 8476 := by
  sorry

/-- A Hadamard matrix of order `2884 = 4 · 103 · 7` exists.  Table 4 of
arXiv:2411.18897v2 carries the entry `721(3)`: no such matrix recorded. -/
theorem hadamard_2884 : HadamardExists 2884 := by
  sorry

/-- A Hadamard matrix of order `4532 = 4 · 103 · 11` exists.  Table 4 of
arXiv:2411.18897v2 carries the entry `1133(3)`: no such matrix recorded. -/
theorem hadamard_4532 : HadamardExists 4532 := by
  sorry

/-- A Hadamard matrix of order `7004 = 4 · 103 · 17` exists.  Table 4 of
arXiv:2411.18897v2 carries the entry `1751(3)`: no such matrix recorded. -/
theorem hadamard_7004 : HadamardExists 7004 := by
  sorry

/-- A Hadamard matrix of order `7828 = 4 · 103 · 19` exists.  Table 4 of
arXiv:2411.18897v2 carries the entry `1957(3)`: no such matrix recorded. -/
theorem hadamard_7828 : HadamardExists 7828 := by
  sorry

/-- A Hadamard matrix of order `9476 = 4 · 103 · 23` exists.  Table 4 of
arXiv:2411.18897v2 carries the entry `2369(3)`: no such matrix recorded. -/
theorem hadamard_9476 : HadamardExists 9476 := by
  sorry

/-- A Hadamard matrix of order `11948 = 4 · 103 · 29` exists.  Table 4 of
arXiv:2411.18897v2 carries the entry `2987(3)`: no such matrix recorded. -/
theorem hadamard_11948 : HadamardExists 11948 := by
  sorry

end HadamardFormal
