/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import HadamardFormal.Defs
import HadamardFormal.GoethalsSeidel

/-!
# The Cooper--Wallis composition

This file implements the Williamson-array sign table on the product cyclic
group.  The resulting four sign matrices are group-developed, so they supply
the algebraic hypotheses of the Goethals--Seidel array.
-/

namespace HadamardFormalCore

open scoped BigOperators Matrix

/-- A sequence on the product of two cyclic index groups. -/
abbrev ProductSequence (t w : ℕ) := Fin t × Fin w → ℤ

/-- The sign in column `i` of row `j` of the Williamson array. -/
def cooperWallisSign : Fin 4 → Fin 4 → ℤ :=
  ![
    ![1, 1, 1, 1],
    ![-1, 1, 1, -1],
    ![-1, -1, 1, 1],
    ![-1, 1, -1, 1]
  ]

/-- The Williamson component used in column `i` of row `j`.  The values
`0,1,2,3` stand for `A,B,C,D`. -/
def cooperWallisPermutation : Fin 4 → Fin 4 → Fin 4 :=
  ![
    ![0, 1, 2, 3],
    ![1, 0, 3, 2],
    ![2, 3, 0, 1],
    ![3, 2, 1, 0]
  ]

/-- The four product-group sequences in the Cooper--Wallis construction.

Expanding the four rows gives exactly

`T₁A + T₂B + T₃C + T₄D`,
`−T₁B + T₂A + T₃D − T₄C`,
`−T₁C − T₂D + T₃A + T₄B`, and
`−T₁D + T₂C − T₃B + T₄A`.
-/
def cooperWallisSequences {t w : ℕ} (T : Quadruple t) (W : Quadruple w) :
    Fin 4 → ProductSequence t w :=
  fun j z ↦ ∑ i, cooperWallisSign j i * T i z.1 * W (cooperWallisPermutation j i) z.2

/-- A matrix developed from a sequence on a finite additive group, using the
same source orientation `x (j - i)` as `circulant`. -/
def developedMatrix {G : Type*} [Sub G] (x : G → ℤ) : Matrix G G ℤ :=
  fun i j ↦ x (j - i)

@[simp]
theorem developedMatrix_apply {G : Type*} [Sub G] (x : G → ℤ) (i j : G) :
    developedMatrix x i j = x (j - i) :=
  rfl

/-- Negation as an involutive permutation of an additive group. -/
def negationPerm (G : Type*) [AddGroup G] : Equiv.Perm G where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x

@[simp]
theorem negationPerm_apply {G : Type*} [AddGroup G] (x : G) :
    negationPerm G x = -x :=
  rfl

theorem negationPerm_involutive {G : Type*} [AddGroup G] :
    Function.Involutive (negationPerm G) := by
  intro x
  simp

/-- Transposition reverses the developing sequence. -/
theorem developedMatrix_transpose {G : Type*} [AddCommGroup G] (x : G → ℤ) :
    (developedMatrix x).transpose = developedMatrix (fun q ↦ x (-q)) := by
  ext i j
  change x (i - j) = x (-(j - i))
  congr 1
  abel

/-- Every matrix developed over an abelian group is type one for inversion. -/
theorem developedMatrix_isTypeOne {G : Type*} [AddCommGroup G] (x : G → ℤ) :
    IsTypeOne (negationPerm G) (developedMatrix x) := by
  intro i j
  change x (i - -j) = x (j - -i)
  congr 1
  abel

/-- The involution `q ↦ d - q`, used to commute finite convolutions. -/
private abbrev convolutionFlip {G : Type*} [AddCommGroup G] (d : G) : Equiv.Perm G :=
  Equiv.subLeft d

/-- Matrices developed over the same finite abelian group commute. -/
theorem developedMatrix_mul_comm {G : Type*} [Fintype G] [AddCommGroup G]
    (x y : G → ℤ) :
    developedMatrix x * developedMatrix y = developedMatrix y * developedMatrix x := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ k, x (k - i) * y (j - k)) =
        ∑ q, x q * y ((j - i) - q) := by
      rw [← Equiv.sum_comp (Equiv.addRight i)
        (fun k ↦ x (k - i) * y (j - k))]
      apply Finset.sum_congr rfl
      intro q _
      change x ((q + i) - i) * y (j - (q + i)) =
        x q * y ((j - i) - q)
      congr 2 <;> abel_nf
    _ = ∑ q, y q * x ((j - i) - q) := by
      rw [← Equiv.sum_comp (convolutionFlip (j - i))
        (fun q ↦ y q * x ((j - i) - q))]
      apply Finset.sum_congr rfl
      intro q _
      dsimp [convolutionFlip, Equiv.subLeft]
      rw [mul_comm]
      congr 2; abel_nf
    _ = ∑ k, y (k - i) * x (j - k) := by
      rw [← Equiv.sum_comp (Equiv.addRight i)
        (fun k ↦ y (k - i) * x (j - k))]
      apply Finset.sum_congr rfl
      intro q _
      change y q * x ((j - i) - q) =
        y ((q + i) - i) * x (j - (q + i))
      congr 2
      · abel_nf
      · abel_nf

/-- A developed matrix also commutes with every transposed developed matrix. -/
theorem developedMatrix_mul_transpose_comm {G : Type*} [Fintype G] [AddCommGroup G]
    (x y : G → ℤ) :
    developedMatrix x * (developedMatrix y).transpose =
      (developedMatrix y).transpose * developedMatrix x := by
  rw [developedMatrix_transpose]
  exact developedMatrix_mul_comm _ _

/-- The four group-developed matrices supplied to the Goethals--Seidel array. -/
def cooperWallisMatrices {t w : ℕ} [NeZero t] [NeZero w]
    (T : Quadruple t) (W : Quadruple w) :
    Fin 4 → Matrix (Fin t × Fin w) (Fin t × Fin w) ℤ :=
  fun j ↦ developedMatrix (cooperWallisSequences T W j)

private theorem IsSign.mul {a b : ℤ} (ha : IsSign a) (hb : IsSign b) :
    IsSign (a * b) := by
  rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl) <;>
    simp [IsSign]

theorem cooperWallisSign_isSign (j i : Fin 4) :
    IsSign (cooperWallisSign j i) := by
  fin_cases j <;> fin_cases i <;> simp [cooperWallisSign, IsSign]

/-- The support-count formulation of a T-matrix supplies a unique nonzero
component at each cyclic position. -/
theorem tMatrix_uniqueSupport {t : ℕ} [NeZero t] {T : Quadruple t}
    (hT : IsTMatrixQuadruple T) (q : Fin t) :
    ∃ k : Fin 4, T k q ≠ 0 ∧ ∀ i, i ≠ k → T i q = 0 := by
  have hcard : (Finset.univ.filter fun i ↦ T i q ≠ 0).card = 1 := by
    simpa [supportCount] using hT.2.1 q
  rcases Finset.card_eq_one.mp hcard with ⟨k, hk⟩
  refine ⟨k, ?_, ?_⟩
  · have : k ∈ Finset.univ.filter fun i ↦ T i q ≠ 0 := by
      rw [hk]
      simp
    simpa using this
  · intro i hik
    by_contra hi
    have hi' : i ∈ Finset.univ.filter fun a ↦ T a q ≠ 0 := by
      simp [hi]
    rw [hk] at hi'
    exact hik (by simpa using hi')

/-- Every entry of each Cooper--Wallis product sequence is a sign. -/
theorem cooperWallisSequences_isSign {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) :
    ∀ j z, IsSign (cooperWallisSequences T W j z) := by
  intro j z
  rcases tMatrix_uniqueSupport hT z.1 with ⟨k, hk, hkzero⟩
  have hTk : IsSign (T k z.1) := by
    rcases hT.1 k z.1 with hzero | hsign
    · exact False.elim (hk hzero)
    · exact hsign
  have hsingle : cooperWallisSequences T W j z =
      cooperWallisSign j k * T k z.1 * W (cooperWallisPermutation j k) z.2 := by
    unfold cooperWallisSequences
    apply Finset.sum_eq_single k
    · intro i _ hik
      rw [hkzero i hik]
      ring
    · simp
  rw [hsingle]
  exact (cooperWallisSign_isSign j k).mul hTk |>.mul
    (hW.1 (cooperWallisPermutation j k) z.2)

/-- Periodic cross-correlation on a finite additive group. -/
def groupCorrelation {G : Type*} [Fintype G] [Add G]
    (x y : G → ℤ) (s : G) : ℤ :=
  ∑ q, x q * y (q + s)

/-- Periodic autocorrelation on a finite additive group. -/
def groupPaf {G : Type*} [Fintype G] [Add G] (x : G → ℤ) (s : G) : ℤ :=
  groupCorrelation x x s

@[simp]
theorem groupPaf_fin_eq_paf {n : ℕ} [NeZero n] (x : Sequence n) (s : Fin n) :
    groupPaf x s = paf x s :=
  rfl

/-- The involution `q ↦ -(q+s)` used to swap symmetric correlations. -/
private def correlationFlip {G : Type*} [AddCommGroup G] (s : G) : Equiv.Perm G :=
  (Equiv.addRight s).trans (negationPerm G)

/-- Cross-correlation is symmetric in two reversal-invariant sequences. -/
theorem groupCorrelation_comm_of_symmetric {G : Type*} [Fintype G] [AddCommGroup G]
    {x y : G → ℤ} (hx : ∀ q, x (-q) = x q) (hy : ∀ q, y (-q) = y q)
    (s : G) : groupCorrelation x y s = groupCorrelation y x s := by
  unfold groupCorrelation
  rw [← Equiv.sum_comp (correlationFlip s) (fun q ↦ x q * y (q + s))]
  apply Finset.sum_congr rfl
  intro q _
  change x (-(q + s)) * y (-(q + s) + s) = y q * x (q + s)
  rw [hx (q + s)]
  have harg : -(q + s) + s = -q := by abel
  rw [harg, hy q, mul_comm]

/-- A pure tensor of two sequences, viewed as a sequence on their product. -/
def tensorSequence {G K : Type*} (x : G → ℤ) (y : K → ℤ) : G × K → ℤ :=
  fun z ↦ x z.1 * y z.2

/-- Correlation of pure tensors factors into the product of correlations. -/
theorem groupCorrelation_tensor {G K : Type*} [Fintype G] [Fintype K]
    [Add G] [Add K] (x x' : G → ℤ) (y y' : K → ℤ) (s : G × K) :
    groupCorrelation (tensorSequence x y) (tensorSequence x' y') s =
      groupCorrelation x x' s.1 * groupCorrelation y y' s.2 := by
  unfold groupCorrelation tensorSequence
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- Correlation is additive in its first sequence argument. -/
private theorem groupCorrelation_sum_left {I G : Type*} [Fintype I] [Fintype G]
    [Add G] (f : I → G → ℤ) (y : G → ℤ) (s : G) :
    groupCorrelation (fun q ↦ ∑ i, f i q) y s =
      ∑ i, groupCorrelation (f i) y s := by
  unfold groupCorrelation
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

/-- Correlation is additive in its second sequence argument. -/
private theorem groupCorrelation_sum_right {I G : Type*} [Fintype I] [Fintype G]
    [Add G] (x : G → ℤ) (f : I → G → ℤ) (s : G) :
    groupCorrelation x (fun q ↦ ∑ i, f i q) s =
      ∑ i, groupCorrelation x (f i) s := by
  unfold groupCorrelation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- Correlation of scalar-weighted pure tensors. -/
private theorem groupCorrelation_weightedTensor {G K : Type*}
    [Fintype G] [Fintype K] [Add G] [Add K]
    (c d : ℤ) (x x' : G → ℤ) (y y' : K → ℤ) (s : G × K) :
    groupCorrelation
        (fun z ↦ c * x z.1 * y z.2)
        (fun z ↦ d * x' z.1 * y' z.2) s =
      c * d * groupCorrelation x x' s.1 * groupCorrelation y y' s.2 := by
  calc
    groupCorrelation
          (fun z ↦ c * x z.1 * y z.2)
          (fun z ↦ d * x' z.1 * y' z.2) s =
        c * d * groupCorrelation (tensorSequence x y) (tensorSequence x' y') s := by
      unfold groupCorrelation tensorSequence
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = c * d * groupCorrelation x x' s.1 * groupCorrelation y y' s.2 := by
      rw [groupCorrelation_tensor]
      ring

/-- Expanded correlation formula for one Cooper--Wallis output row. -/
theorem cooperWallisSequences_correlation {t w : ℕ} [NeZero t] [NeZero w]
    (T : Quadruple t) (W : Quadruple w) (j : Fin 4) (s : Fin t × Fin w) :
    groupPaf (cooperWallisSequences T W j) s =
      ∑ i, ∑ k,
        cooperWallisSign j i * cooperWallisSign j k *
          groupCorrelation (T i) (T k) s.1 *
            groupCorrelation (W (cooperWallisPermutation j i))
              (W (cooperWallisPermutation j k)) s.2 := by
  unfold groupPaf cooperWallisSequences
  rw [groupCorrelation_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [groupCorrelation_sum_right]
  apply Finset.sum_congr rfl
  intro k _
  exact groupCorrelation_weightedTensor _ _ _ _ _ _ _

/-- The Williamson sign table has the required orthogonality: diagonal
columns sum to the aggregate Williamson PAF, while distinct columns cancel. -/
theorem cooperWallis_williamsonTable {w : ℕ} [NeZero w] {W : Quadruple w}
    (hsym : ∀ i, IsSymmetricSequence (W i)) (i k : Fin 4) (s : Fin w) :
    (∑ j, cooperWallisSign j i * cooperWallisSign j k *
      groupCorrelation (W (cooperWallisPermutation j i))
        (W (cooperWallisPermutation j k)) s) =
      if i = k then ∑ a, groupPaf (W a) s else 0 := by
  have hcorr (a b : Fin 4) :
      groupCorrelation (W a) (W b) s = groupCorrelation (W b) (W a) s :=
    groupCorrelation_comm_of_symmetric (hsym a) (hsym b) s
  fin_cases i <;> fin_cases k <;>
    simp [cooperWallisSign, cooperWallisPermutation, groupPaf,
      Fin.sum_univ_succ, hcorr] <;> ring

/-- The aggregate PAF of the four product sequences factors as the aggregate
T-matrix PAF times the aggregate Williamson PAF. -/
theorem cooperWallis_aggregatePaf_factor {t w : ℕ} [NeZero t] [NeZero w]
    (T : Quadruple t) (W : Quadruple w)
    (hsym : ∀ i, IsSymmetricSequence (W i)) (s : Fin t × Fin w) :
    (∑ j, groupPaf (cooperWallisSequences T W j) s) =
      (∑ i, groupPaf (T i) s.1) * (∑ a, groupPaf (W a) s.2) := by
  simp_rw [cooperWallisSequences_correlation]
  calc
    (∑ j, ∑ i, ∑ k,
        cooperWallisSign j i * cooperWallisSign j k *
          groupCorrelation (T i) (T k) s.1 *
            groupCorrelation (W (cooperWallisPermutation j i))
              (W (cooperWallisPermutation j k)) s.2) =
        ∑ i, ∑ k, groupCorrelation (T i) (T k) s.1 *
          (∑ j, cooperWallisSign j i * cooperWallisSign j k *
            groupCorrelation (W (cooperWallisPermutation j i))
              (W (cooperWallisPermutation j k)) s.2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ k, groupCorrelation (T i) (T k) s.1 *
          (if i = k then ∑ a, groupPaf (W a) s.2 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [cooperWallis_williamsonTable hsym]
    _ = ∑ i, groupPaf (T i) s.1 * (∑ a, groupPaf (W a) s.2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp [groupPaf]
      · intro k _ hki
        simp [Ne.symm hki]
      · simp
    _ = (∑ i, groupPaf (T i) s.1) * (∑ a, groupPaf (W a) s.2) := by
      rw [Finset.sum_mul]

/-- The Cooper--Wallis product sequences have aggregate PAF concentrated at
the zero of the product group. -/
theorem cooperWallis_aggregatePaf {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) (s : Fin t × Fin w) :
    (∑ j, groupPaf (cooperWallisSequences T W j) s) =
      (4 * (t * w) : ℤ) * if s = 0 then 1 else 0 := by
  rw [cooperWallis_aggregatePaf_factor T W hW.2.1]
  simp_rw [groupPaf_fin_eq_paf]
  rw [hT.2.2 s.1, hW.2.2 s.2]
  rcases s with ⟨st, sw⟩
  by_cases ht : st = 0
  · subst st
    by_cases hw : sw = 0
    · subst sw
      simp [deltaZero]
      ring
    · have hs : ((0, sw) : Fin t × Fin w) ≠ 0 := by
        intro h
        exact hw (congrArg Prod.snd h)
      simp [deltaZero, hw, hs]
  · have hs : ((st, sw) : Fin t × Fin w) ≠ 0 := by
      intro h
      exact ht (congrArg Prod.fst h)
    simp [deltaZero, ht, hs]

/-- A developed matrix times its transpose reads the PAF of its developing
sequence at the row difference. -/
theorem developedMatrix_mul_transpose_apply {G : Type*} [Fintype G]
    [AddCommGroup G] (x : G → ℤ) (i j : G) :
    (developedMatrix x * (developedMatrix x).transpose) i j =
      groupPaf x (i - j) := by
  rw [Matrix.mul_apply]
  unfold groupPaf groupCorrelation
  rw [← Equiv.sum_comp (Equiv.addRight i)
    (fun k ↦ developedMatrix x i k * (developedMatrix x).transpose k j)]
  apply Finset.sum_congr rfl
  intro q _
  change x ((q + i) - i) * x ((q + i) - j) = x q * x (q + (i - j))
  congr 2
  · abel_nf
  · abel_nf

/-- The four Cooper--Wallis matrices satisfy the aggregate orthogonality
identity required by Goethals--Seidel. -/
theorem cooperWallisMatrices_aggregate {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) :
    (∑ a, cooperWallisMatrices T W a * (cooperWallisMatrices T W a).transpose) =
      (4 * Fintype.card (Fin t × Fin w) : ℤ) •
        (1 : Matrix (Fin t × Fin w) (Fin t × Fin w) ℤ) := by
  ext i j
  simp only [Matrix.sum_apply, cooperWallisMatrices]
  simp_rw [developedMatrix_mul_transpose_apply]
  rw [cooperWallis_aggregatePaf hT hW (i - j)]
  by_cases hij : i = j
  · subst j
    simp [Fintype.card_prod]
  · have hd : i - j ≠ 0 := sub_ne_zero.mpr hij
    simp [hd, hij, Fintype.card_prod]

/-- The Cooper--Wallis matrices commute pairwise. -/
theorem cooperWallisMatrices_mul_comm {t w : ℕ} [NeZero t] [NeZero w]
    (T : Quadruple t) (W : Quadruple w) (a b : Fin 4) :
    cooperWallisMatrices T W a * cooperWallisMatrices T W b =
      cooperWallisMatrices T W b * cooperWallisMatrices T W a := by
  exact developedMatrix_mul_comm _ _

/-- The Cooper--Wallis matrices commute with all transposed members of the
family. -/
theorem cooperWallisMatrices_mul_transpose_comm {t w : ℕ}
    [NeZero t] [NeZero w] (T : Quadruple t) (W : Quadruple w) (a b : Fin 4) :
    cooperWallisMatrices T W a * (cooperWallisMatrices T W b).transpose =
      (cooperWallisMatrices T W b).transpose * cooperWallisMatrices T W a := by
  exact developedMatrix_mul_transpose_comm _ _

/-- The Cooper--Wallis matrices are type one for product-group inversion. -/
theorem cooperWallisMatrices_isTypeOne {t w : ℕ} [NeZero t] [NeZero w]
    (T : Quadruple t) (W : Quadruple w) (a : Fin 4) :
    IsTypeOne (negationPerm (Fin t × Fin w)) (cooperWallisMatrices T W a) :=
  developedMatrix_isTypeOne _

/-- Every entry of the four Cooper--Wallis matrices is a sign. -/
theorem cooperWallisMatrices_isSign {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) :
    ∀ a i j, IsSign (cooperWallisMatrices T W a i j) := by
  intro a i j
  exact cooperWallisSequences_isSign hT hW a (j - i)

/-- The symbolic Cooper--Wallis/Goethals--Seidel matrix is Hadamard on its
natural product index type. -/
theorem cooperWallis_isHadamardOn {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) :
    IsHadamardOn
      (goethalsSeidel (negationPerm (Fin t × Fin w))
        (cooperWallisMatrices T W)) := by
  apply goethalsSeidel_isHadamard
  · exact negationPerm_involutive
  · exact cooperWallisMatrices_isSign hT hW
  · exact cooperWallisMatrices_mul_comm T W
  · exact cooperWallisMatrices_mul_transpose_comm T W
  · exact cooperWallisMatrices_isTypeOne T W
  · exact cooperWallisMatrices_aggregate hT hW

/-- Cooper--Wallis existence theorem: a periodic T-matrix quadruple of order
`t` and a Williamson quadruple of order `w` produce a Hadamard matrix of order
`4*t*w`. -/
theorem cooperWallis {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) :
    HadamardExists (4 * t * w) := by
  let H := goethalsSeidel (negationPerm (Fin t × Fin w))
    (cooperWallisMatrices T W)
  have hH : IsHadamardOn H := cooperWallis_isHadamardOn hT hW
  have hex : HadamardExists (Fintype.card (Fin 4 × (Fin t × Fin w))) :=
    ⟨toFinMatrix H, isHadamard_toFin hH⟩
  simpa [Fintype.card_prod, Nat.mul_assoc] using hex

end HadamardFormalCore
