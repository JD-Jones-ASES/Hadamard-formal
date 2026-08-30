/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-!
# Core definitions for the Hadamard formalization

This file fixes the mathematical conventions used throughout the project.  In
particular, `circulant x` uses the Hadamard-T orientation

`circulant x i j = x (j - i)`,

and `paf` is periodic autocorrelation on `Fin n`.
-/

namespace HadamardFormalCore

open scoped BigOperators

/-- An integer is a Hadamard sign when it is `+1` or `-1`. -/
def IsSign (z : ℤ) : Prop :=
  z = 1 ∨ z = -1

/-- `IsSign` is computable, so concrete sign data can be checked by kernel
reduction. -/
instance instDecidableIsSign (z : ℤ) : Decidable (IsSign z) := by
  unfold IsSign
  infer_instance

/-- A Hadamard matrix indexed by an arbitrary finite type.

This is the integer specialization of mathlib's `Matrix.IsHadamard`: its
unitary-entry condition is exactly `+1` or `-1`, and its two orthogonality
identities are the square-matrix form of the classical condition.  The `Fin n`
statement surface is `IsHadamard` below. -/
abbrev IsHadamardOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℤ) : Prop :=
  H.IsHadamard

/-- A classical integer Hadamard matrix of order `n`. -/
abbrev IsHadamard {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsHadamardOn H

/-- There exists a classical integer Hadamard matrix of order `n`. -/
def HadamardExists (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, IsHadamard H

/-- Simultaneously relabel the rows and columns of a square matrix. -/
def reindexSquare {ι κ : Type*} (e : ι ≃ κ) (H : Matrix ι ι ℤ) : Matrix κ κ ℤ :=
  Matrix.reindex e e H

@[simp]
theorem reindexSquare_apply {ι κ : Type*} (e : ι ≃ κ) (H : Matrix ι ι ℤ)
    (i j : κ) : reindexSquare e H i j = H (e.symm i) (e.symm j) :=
  rfl

/-- Entries of an integer Hadamard matrix are signs in the source sense. -/
theorem isSign_of_isHadamardOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℤ} (hH : IsHadamardOn H) (i j : ι) : IsSign (H i j) :=
  Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j)

/-- Hadamardness is preserved when the common row/column index type is
relabelled by an equivalence. -/
theorem isHadamardOn_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {H : Matrix ι ι ℤ} (hH : IsHadamardOn H)
    (e : ι ≃ κ) : IsHadamardOn (reindexSquare e H) :=
  hH.reindex e e

/-- Reindex an arbitrary finite Hadamard matrix by the canonical equivalence
with `Fin (Fintype.card ι)`. -/
noncomputable def toFinMatrix {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℤ) : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℤ :=
  reindexSquare (Fintype.equivFin ι) H

/-- The canonical `Fin` reindexing of a Hadamard matrix is Hadamard. -/
theorem isHadamard_toFin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℤ} (hH : IsHadamardOn H) : IsHadamard (toFinMatrix H) := by
  exact isHadamardOn_reindex hH (Fintype.equivFin ι)

/-- An integer sequence indexed by the cyclic group `Fin n`. -/
abbrev Sequence (n : ℕ) := Fin n → ℤ

/-- Four integer sequences of a common order. -/
abbrev Quadruple (n : ℕ) := Fin 4 → Sequence n

/-- The circulant matrix whose first row is `x`, with source orientation
`x[(j-i) mod n]`. -/
def circulant {n : ℕ} [NeZero n] (x : Sequence n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => x (j - i)

@[simp]
theorem circulant_apply {n : ℕ} [NeZero n] (x : Sequence n) (i j : Fin n) :
    circulant x i j = x (j - i) :=
  rfl

/-- Periodic autocorrelation, `PAF(x)(s) = sum_q x[q] x[q+s]`. -/
def paf {n : ℕ} [NeZero n] (x : Sequence n) (s : Fin n) : ℤ :=
  ∑ q, x q * x (q + s)

/-- The integer delta function at zero on `Fin n`. -/
def deltaZero {n : ℕ} [NeZero n] (s : Fin n) : ℤ :=
  if s = 0 then 1 else 0

@[simp]
theorem deltaZero_zero {n : ℕ} [NeZero n] : deltaZero (0 : Fin n) = 1 := by
  simp [deltaZero]

@[simp]
theorem deltaZero_eq_zero {n : ℕ} [NeZero n] {s : Fin n} (hs : s ≠ 0) :
    deltaZero s = 0 := by
  simp [deltaZero, hs]

/-- The alphabet for a T-matrix entry. -/
def IsTEntry (z : ℤ) : Prop :=
  z = 0 ∨ IsSign z

/-- `IsTEntry` is computable. -/
instance instDecidableIsTEntry (z : ℤ) : Decidable (IsTEntry z) := by
  unfold IsTEntry
  infer_instance

/-- The number of nonzero components at one position of a quadruple. -/
def supportCount {n : ℕ} (T : Quadruple n) (q : Fin n) : ℕ :=
  (Finset.univ.filter fun i => T i q ≠ 0).card

/-- A periodic T-matrix quadruple of order `n`.

Exactly one component is nonzero at each cyclic position, and the aggregate
periodic autocorrelation is `n * deltaZero`.  This is intentionally the
periodic Cooper--Wallis input, not the stronger aperiodic T-sequence notion. -/
def IsTMatrixQuadruple {n : ℕ} [NeZero n] (T : Quadruple n) : Prop :=
  (∀ i q, IsTEntry (T i q)) ∧
    (∀ q, supportCount T q = 1) ∧
      ∀ s, ∑ i, paf (T i) s = (n : ℤ) * deltaZero s

/-- The periodic T-matrix predicate is decidable on concrete data. -/
instance instDecidableIsTMatrixQuadruple {n : ℕ} [NeZero n] (T : Quadruple n) :
    Decidable (IsTMatrixQuadruple T) := by
  unfold IsTMatrixQuadruple
  infer_instance

/-- The four circulant matrices carried by a sequence quadruple. -/
def quadrupleCirculants {n : ℕ} [NeZero n] (T : Quadruple n) :
    Fin 4 → Matrix (Fin n) (Fin n) ℤ :=
  fun i => circulant (T i)

/-- A cyclic sequence is symmetric when reversing its index fixes it. -/
def IsSymmetricSequence {n : ℕ} [NeZero n] (x : Sequence n) : Prop :=
  ∀ q, x (-q) = x q

/-- Cyclic symmetry of a concrete sequence is decidable. -/
instance instDecidableIsSymmetricSequence {n : ℕ} [NeZero n] (x : Sequence n) :
    Decidable (IsSymmetricSequence x) := by
  unfold IsSymmetricSequence
  infer_instance

/-- A symmetric first row gives a symmetric circulant matrix. -/
theorem circulant_transpose_eq_self {n : ℕ} [NeZero n] {x : Sequence n}
    (hx : IsSymmetricSequence x) : (circulant x).transpose = circulant x := by
  ext i j
  change x (i - j) = x (j - i)
  rw [show i - j = -(j - i) by abel]
  exact hx (j - i)

/-- A symmetric-circulant Williamson quadruple of order `n`.

The data are represented by their four first rows.  Each row is a sign
sequence fixed by cyclic reversal, and their aggregate periodic
autocorrelation is `4*n * deltaZero`. -/
def IsWilliamson {n : ℕ} [NeZero n] (W : Quadruple n) : Prop :=
  (∀ i q, IsSign (W i q)) ∧
    (∀ i, IsSymmetricSequence (W i)) ∧
      ∀ s, ∑ i, paf (W i) s = 4 * (n : ℤ) * deltaZero s

/-- The Williamson predicate is decidable on concrete data. -/
instance instDecidableIsWilliamson {n : ℕ} [NeZero n] (W : Quadruple n) :
    Decidable (IsWilliamson W) := by
  unfold IsWilliamson
  infer_instance

end HadamardFormalCore
