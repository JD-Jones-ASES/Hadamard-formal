/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import HadamardFormal.Defs

/-!
# The Goethals--Seidel array

This file formalizes the standard four-by-four block array.  The reversal is
kept abstract: it is an involutive permutation of the common row and column
index type.  This covers the usual back-identity permutation as well as the
group inversion permutation used by group-developed matrices.
-/

namespace HadamardFormalCore

open scoped BigOperators Matrix

/-- Reverse the columns of a square matrix along a permutation. -/
def reverseColumns {ι : Type*} (r : Equiv.Perm ι) (A : Matrix ι ι ℤ) :
    Matrix ι ι ℤ :=
  fun i j => A i (r j)

@[simp]
theorem reverseColumns_apply {ι : Type*} (r : Equiv.Perm ι)
    (A : Matrix ι ι ℤ) (i j : ι) : reverseColumns r A i j = A i (r j) :=
  rfl

@[simp]
theorem reverseColumns_neg {ι : Type*} (r : Equiv.Perm ι)
    (A : Matrix ι ι ℤ) : reverseColumns r (-A) = -reverseColumns r A := by
  rfl

@[simp]
theorem reverseColumns_reverseColumns {ι : Type*} (r : Equiv.Perm ι)
    (hr : Function.Involutive r) (A : Matrix ι ι ℤ) :
    reverseColumns r (reverseColumns r A) = A := by
  ext i j
  simp only [reverseColumns_apply]
  rw [hr j]

/-- The entrywise form of `Aᵀ R = R A`, where `R` is the permutation
matrix of `r`. -/
def IsTypeOne {ι : Type*} (r : Equiv.Perm ι) (A : Matrix ι ι ℤ) : Prop :=
  ∀ i j, A (r j) i = A (r i) j

/-- The four-by-four matrix of blocks in the standard Goethals--Seidel
array. -/
def goethalsSeidelBlock {ι : Type*} (r : Equiv.Perm ι)
    (X : Fin 4 → Matrix ι ι ℤ) : Fin 4 → Fin 4 → Matrix ι ι ℤ :=
  ![
    ![X 0, reverseColumns r (X 1), reverseColumns r (X 2),
      reverseColumns r (X 3)],
    ![-reverseColumns r (X 1), X 0, -reverseColumns r (X 3).transpose,
      reverseColumns r (X 2).transpose],
    ![-reverseColumns r (X 2), reverseColumns r (X 3).transpose, X 0,
      -reverseColumns r (X 1).transpose],
    ![-reverseColumns r (X 3), -reverseColumns r (X 2).transpose,
      reverseColumns r (X 1).transpose, X 0]
  ]

/-- The Goethals--Seidel block array as one matrix, indexed by a block index
and an index inside the block. -/
def goethalsSeidel {ι : Type*} (r : Equiv.Perm ι)
    (X : Fin 4 → Matrix ι ι ℤ) :
    Matrix (Fin 4 × ι) (Fin 4 × ι) ℤ :=
  fun i j => goethalsSeidelBlock r X i.1 j.1 i.2 j.2

@[simp]
theorem goethalsSeidel_apply {ι : Type*} (r : Equiv.Perm ι)
    (X : Fin 4 → Matrix ι ι ℤ) (i j : Fin 4 × ι) :
    goethalsSeidel r X i j = goethalsSeidelBlock r X i.1 j.1 i.2 j.2 :=
  rfl

theorem isTypeOne_transpose {ι : Type*} (r : Equiv.Perm ι)
    (hr : Function.Involutive r) {A : Matrix ι ι ℤ}
    (hA : IsTypeOne r A) : IsTypeOne r A.transpose := by
  intro i j
  change A i (r j) = A j (r i)
  have h := (hA (r i) (r j)).symm
  rw [hr i, hr j] at h
  exact h

theorem reverseColumns_mul_transpose_reverseColumns {ι : Type*} [Fintype ι]
    (r : Equiv.Perm ι) (A B : Matrix ι ι ℤ) :
    reverseColumns r A * (reverseColumns r B).transpose = A * B.transpose := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, reverseColumns_apply]
  exact Equiv.sum_comp r (fun k => A i k * B j k)

theorem mul_transpose_reverseColumns {ι : Type*} [Fintype ι]
    (r : Equiv.Perm ι) (hr : Function.Involutive r)
    (A B : Matrix ι ι ℤ) (hB : IsTypeOne r B) :
    A * (reverseColumns r B).transpose = reverseColumns r (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, reverseColumns_apply]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have h := (hB (r j) (r k)).symm
  rw [hr j, hr k] at h
  exact h

theorem reverseColumns_mul_transpose {ι : Type*} [Fintype ι]
    (r : Equiv.Perm ι) (hr : Function.Involutive r)
    (A B : Matrix ι ι ℤ) (hB : IsTypeOne r B) :
    reverseColumns r A * B.transpose = reverseColumns r (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, reverseColumns_apply]
  calc
    ∑ k, A i (r k) * B j k =
        ∑ k, A i (r k) * B (r k) (r j) := by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          have h := (hB (r j) k).symm
          rw [hr j] at h
          exact h
    _ = ∑ k, A i k * B k (r j) :=
      Equiv.sum_comp r (fun k => A i k * B k (r j))

theorem reverseColumns_reverseColumns_mul {ι : Type*} [Fintype ι]
    (r : Equiv.Perm ι) (hr : Function.Involutive r)
    (A B : Matrix ι ι ℤ) (hB : IsTypeOne r B) :
    reverseColumns r (reverseColumns r A * B) = A * B.transpose := by
  ext i j
  simp only [reverseColumns_apply, Matrix.mul_apply, Matrix.transpose_apply]
  calc
    ∑ k, A i (r k) * B k (r j) =
        ∑ k, A i (r k) * B (r (r k)) (r j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hr k]
    _ =
        ∑ k, A i k * B (r k) (r j) :=
      Equiv.sum_comp r (fun k => A i k * B (r k) (r j))
    _ = ∑ k, A i k * B j k := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      have h := hB (r j) k
      rw [hr j] at h
      exact h

theorem goethalsSeidel_mul_transpose_apply {ι : Type*} [Fintype ι]
    (r : Equiv.Perm ι) (X : Fin 4 → Matrix ι ι ℤ)
    (a b : Fin 4) (i j : ι) :
    (goethalsSeidel r X * (goethalsSeidel r X).transpose) (a, i) (b, j) =
      (∑ k, goethalsSeidelBlock r X a k *
        (goethalsSeidelBlock r X b k).transpose) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, goethalsSeidel_apply,
    Matrix.sum_apply]
  rw [← Finset.sum_product' Finset.univ Finset.univ]
  simp only [Finset.univ_product_univ]

theorem goethalsSeidel_block_mul_transpose {ι : Type*} [Fintype ι]
    (r : Equiv.Perm ι) (hr : Function.Involutive r)
    (X : Fin 4 → Matrix ι ι ℤ)
    (hcomm : ∀ a b, X a * X b = X b * X a)
    (hcommTranspose : ∀ a b,
      X a * (X b).transpose = (X b).transpose * X a)
    (htype : ∀ a, IsTypeOne r (X a)) (a b : Fin 4) :
    (∑ k, goethalsSeidelBlock r X a k *
      (goethalsSeidelBlock r X b k).transpose) =
      if a = b then ∑ k, X k * (X k).transpose else 0 := by
  have hcommTT : ∀ a b,
      (X a).transpose * (X b).transpose =
        (X b).transpose * (X a).transpose := by
    intro a b
    have h := congrArg Matrix.transpose (hcomm b a)
    simpa using h
  fin_cases a <;> fin_cases b <;>
    simp [goethalsSeidelBlock, Fin.sum_univ_four,
      mul_transpose_reverseColumns r hr, reverseColumns_mul_transpose r hr,
      reverseColumns_reverseColumns_mul r hr,
      reverseColumns_reverseColumns r hr,
      htype, isTypeOne_transpose r hr, hcomm, hcommTranspose, hcommTT] <;>
    abel

theorem goethalsSeidel_mul_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Equiv.Perm ι) (hr : Function.Involutive r)
    (X : Fin 4 → Matrix ι ι ℤ)
    (hcomm : ∀ a b, X a * X b = X b * X a)
    (hcommTranspose : ∀ a b,
      X a * (X b).transpose = (X b).transpose * X a)
    (htype : ∀ a, IsTypeOne r (X a))
    (haggregate : ∑ a, X a * (X a).transpose =
      (4 * Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ)) :
    goethalsSeidel r X * (goethalsSeidel r X).transpose =
      (Fintype.card (Fin 4 × ι) : ℤ) •
        (1 : Matrix (Fin 4 × ι) (Fin 4 × ι) ℤ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [goethalsSeidel_mul_transpose_apply]
  rw [goethalsSeidel_block_mul_transpose r hr X hcomm hcommTranspose htype]
  by_cases hab : a = b
  · subst b
    by_cases hij : i = j
    · subst j
      simp [haggregate, Fintype.card_prod]
    · simp [haggregate, Fintype.card_prod, hij]
  · simp [hab, Fintype.card_prod]

theorem isSign_neg {z : ℤ} (hz : IsSign z) : IsSign (-z) := by
  rcases hz with hz | hz
  · right
    simp [hz]
  · left
    simp [hz]

theorem goethalsSeidel_isSign {ι : Type*} (r : Equiv.Perm ι)
    (X : Fin 4 → Matrix ι ι ℤ)
    (hsign : ∀ a i j, IsSign (X a i j)) (i j : Fin 4 × ι) :
    IsSign (goethalsSeidel r X i j) := by
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp only [goethalsSeidel, goethalsSeidelBlock]
  all_goals first | exact hsign _ _ _ | exact isSign_neg (hsign _ _ _)

/-- The standard Goethals--Seidel theorem for an involutive reversal.

The two commutation hypotheses say that the four input matrices and their
transposes belong to a common commutative matrix algebra.  In particular,
`hcommTranspose a a` supplies the normality of each input matrix.  These
hypotheses hold for matrices developed over an abelian group. -/
theorem goethalsSeidel_isHadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (r : Equiv.Perm ι) (hr : Function.Involutive r)
    (X : Fin 4 → Matrix ι ι ℤ)
    (hsign : ∀ a i j, IsSign (X a i j))
    (hcomm : ∀ a b, X a * X b = X b * X a)
    (hcommTranspose : ∀ a b,
      X a * (X b).transpose = (X b).transpose * X a)
    (htype : ∀ a, IsTypeOne r (X a))
    (haggregate : ∑ a, X a * (X a).transpose =
      (4 * Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ)) :
    Matrix.IsHadamard (goethalsSeidel r X) := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
      (goethalsSeidel_isSign r X hsign i j)
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact goethalsSeidel_mul_transpose r hr X hcomm hcommTranspose htype haggregate
  · rw [isRegular_iff_ne_zero]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin 4 × ι) ≠ 0)

end HadamardFormalCore
