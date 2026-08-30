/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: OpenAI Codex, Claude Code
-/
import Mathlib
import HadamardFormal.Defs

/-!
# The handshake parity obstruction and the Miyamoto C₂-matrix

An odd-order symmetric integer matrix with zero diagonal, off-diagonal
entries in `{+1, -1}`, and zero row sums has order congruent to `1`
modulo `4`; the class is empty at every positive order not congruent to
`1` modulo `4`; and the displayed C₂-matrix form consumed by Corollary 4
of Miyamoto 1991 therefore has no instance at those block orders.
-/

namespace HadamardFormalCore

/-- A symmetric sign matrix with zero diagonal and zero row sums has order
congruent to one modulo four.  This is the handshake obstruction behind the
Hadamard-M erratum: any instance of Corollary 4 of Miyamoto 1991 forces such
a matrix at the corollary's block order. -/
theorem handshake_mod_four
    (m : ℕ)
    (hm : Odd m)
    (D : Matrix (Fin m) (Fin m) ℤ)
    (hsymm : D.transpose = D)
    (hdiag : ∀ i, D i i = 0)
    (hoff : ∀ i j, i ≠ j → D i j = 1 ∨ D i j = -1)
    (hrow : ∀ i, ∑ j, D i j = 0) :
    m % 4 = 1 := by
  classical
  have hentry_symm (i j : Fin m) : D i j = D j i := by
    have hij := congrFun (congrFun hsymm j) i
    simpa using hij
  let G : SimpleGraph (Fin m) :=
    SimpleGraph.fromRel fun i j ↦ D i j = -1
  have hdegree (i : Fin m) : G.degree i = (m - 1) / 2 := by
    let S : Finset (Fin m) := Finset.univ.erase i
    let N : Finset (Fin m) := S.filter fun j ↦ D i j = -1
    let P : Finset (Fin m) := S.filter fun j ↦ D i j = 1
    have hcover : N ∪ P = S := by
      ext j
      constructor
      · intro hj
        rcases Finset.mem_union.mp hj with hjN | hjP
        · exact (Finset.mem_filter.mp hjN).1
        · exact (Finset.mem_filter.mp hjP).1
      · intro hjS
        have hji : j ≠ i := by simpa [S] using hjS
        rcases hoff i j hji.symm with hij | hij
        · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hjS, hij⟩
        · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr ⟨hjS, hij⟩
    have hdisj : Disjoint N P := by
      refine Finset.disjoint_left.mpr ?_
      intro j hjN hjP
      have hn : D i j = -1 := (Finset.mem_filter.mp hjN).2
      have hp : D i j = 1 := (Finset.mem_filter.mp hjP).2
      omega
    have hcardS : S.card = m - 1 := by
      simp [S]
    have hcard : N.card + P.card = m - 1 := by
      have hu := Finset.card_union_of_disjoint hdisj
      rw [hcover, hcardS] at hu
      omega
    have hrowS : (∑ j ∈ S, D i j) = 0 := by
      have herase := Finset.sum_erase_add (s := Finset.univ) (f := fun j ↦ D i j)
        (Finset.mem_univ i)
      rw [hdiag i, hrow i, add_zero] at herase
      simpa [S] using herase
    have hsumN : (∑ j ∈ N, D i j) = -(N.card : ℤ) := by
      calc
        ∑ j ∈ N, D i j = ∑ _j ∈ N, (-1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (Finset.mem_filter.mp hj).2
        _ = -(N.card : ℤ) := by simp
    have hsumP : (∑ j ∈ P, D i j) = (P.card : ℤ) := by
      calc
        ∑ j ∈ P, D i j = ∑ _j ∈ P, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (Finset.mem_filter.mp hj).2
        _ = (P.card : ℤ) := by simp
    have hsums := Finset.sum_union hdisj (f := fun j ↦ D i j)
    rw [hcover, hrowS, hsumN, hsumP] at hsums
    have hcardN : N.card = (m - 1) / 2 := by omega
    rw [← G.card_neighborFinset_eq_degree]
    have hneighbor : G.neighborFinset i = N := by
      ext j
      constructor
      · intro hj
        have hadjG := (G.mem_neighborFinset i j).mp hj
        have hadjRel : i ≠ j ∧ (D i j = -1 ∨ D j i = -1) := by
          simpa [G] using hadjG
        have hadj : D i j = -1 := by
          rcases hadjRel.2 with hij | hji
          · exact hij
          · exact (hentry_symm i j).trans hji
        exact Finset.mem_filter.mpr ⟨by simp [S, hadjRel.1.symm], hadj⟩
      · intro hj
        have hadj : D i j = -1 := (Finset.mem_filter.mp hj).2
        have hji : j ≠ i := by
          have hjS := (Finset.mem_filter.mp hj).1
          simpa [S] using hjS
        apply (G.mem_neighborFinset i j).mpr
        simpa [G] using And.intro hji.symm (Or.inl hadj)
    rw [hneighbor, hcardN]
  have hsumdeg := G.sum_degrees_eq_twice_card_edges
  simp_rw [hdegree] at hsumdeg
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumdeg
  have hprod_even : Even (m * ((m - 1) / 2)) := by
    refine ⟨G.edgeFinset.card, ?_⟩
    simpa [two_mul] using hsumdeg
  have hhalf_even : Even ((m - 1) / 2) := by
    rcases Nat.even_mul.mp hprod_even with hm_even | hhalf_even
    · exfalso
      rcases hm with ⟨a, ha⟩
      rcases hm_even with ⟨b, hb⟩
      omega
    · exact hhalf_even
  rcases hm with ⟨a, ha⟩
  rcases hhalf_even with ⟨b, hb⟩
  omega

/-- A `±1`-valued function summed over a finite set of odd cardinality has
nonzero sum: every value is odd, so the sum has the parity of the count. -/
theorem sum_sign_ne_zero {α : Type*} (s : Finset α) (hs : Odd s.card)
    (f : α → ℤ) (hf : ∀ a ∈ s, f a = 1 ∨ f a = -1) :
    ∑ a ∈ s, f a ≠ 0 := by
  intro h0
  have hone : ∀ a ∈ s, f a % 2 = 1 := by
    intro a ha
    rcases hf a ha with h | h <;> simp [h]
  have hmod : (∑ a ∈ s, f a) % 2 = (s.card : ℤ) % 2 := by
    rw [Finset.sum_int_mod, Finset.sum_congr rfl hone]
    simp
  rw [h0] at hmod
  have hcard := Nat.odd_iff.mp hs
  omega

/-- For a positive order not congruent to one modulo four, the handshake
class is empty: there is no symmetric integer matrix with zero diagonal,
off-diagonal entries in `{+1, -1}`, and zero row sums.  For odd orders this
is the contrapositive of `handshake_mod_four`; for even orders each row
already carries an odd number of `±1` off-diagonal entries, which cannot sum
to zero. -/
theorem no_handshake_matrix (m : ℕ) (hm0 : 0 < m) (hm : m % 4 ≠ 1) :
    ¬ ∃ D : Matrix (Fin m) (Fin m) ℤ,
        D.transpose = D ∧ (∀ i, D i i = 0) ∧
          (∀ i j, i ≠ j → D i j = 1 ∨ D i j = -1) ∧ ∀ i, ∑ j, D i j = 0 := by
  rintro ⟨D, hsymm, hdiag, hoff, hrow⟩
  rcases Nat.even_or_odd m with he | ho
  · have hme : m % 2 = 0 := Nat.even_iff.mp he
    obtain ⟨i⟩ : Nonempty (Fin m) := ⟨⟨0, hm0⟩⟩
    have herase := Finset.sum_erase_add (s := Finset.univ) (f := fun j ↦ D i j)
      (Finset.mem_univ i)
    rw [hdiag i, hrow i, add_zero] at herase
    have hcard : Odd (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      exact Nat.odd_iff.mpr (by omega)
    have hsigns : ∀ j ∈ Finset.univ.erase i, D i j = 1 ∨ D i j = -1 := by
      intro j hj
      exact hoff i j (Ne.symm (Finset.mem_erase.mp hj).1)
    exact sum_sign_ne_zero _ hcard _ hsigns herase
  · exact hm (handshake_mod_four m ho D hsymm hdiag hoff hrow)

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

/-- The C₂-matrix of Miyamoto 1991's Corollary 4 has no instance at any
positive block order `m` with `m % 4 ≠ 1`: no symmetric interior pair
`D₁, D₂` satisfying the pairing condition of the paper's hypothesis (4.1)
against the identity blocks makes the displayed form satisfy
`D * Dᵀ = 2m • 1`.  The pairing forces `D₁` to have zero diagonal and `±1`
off-diagonal entries, two entries of the product identity force its row
sums to zero, and `no_handshake_matrix` closes the class. -/
theorem no_c2_matrix (m : ℕ) (hm0 : 0 < m) (hm : m % 4 ≠ 1) :
    ¬ ∃ D₁ D₂ : Matrix (Fin m) (Fin m) ℤ,
        D₁.transpose = D₁ ∧ D₂.transpose = D₂ ∧
          (∀ i j, IsSign ((D₁ + 1) i j) ∧ IsSign ((D₁ - 1) i j)) ∧
            (∀ i j, IsSign ((D₂ + 1) i j) ∧ IsSign ((D₂ - 1) i j)) ∧
              c2Display m D₁ D₂ * (c2Display m D₁ D₂).transpose
                = (2 * (m : ℤ)) • 1 := by
  rintro ⟨D₁, D₂, hsymm, -, hpair, -, hprod⟩
  have hdiag : ∀ i, D₁ i i = 0 := by
    intro i
    have hp := (hpair i i).1
    have hq := (hpair i i).2
    simp only [IsSign, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply_eq] at hp hq
    rcases hp with hp | hp <;> rcases hq with hq | hq <;> omega
  have hoff : ∀ i j, i ≠ j → D₁ i j = 1 ∨ D₁ i j = -1 := by
    intro i j hij
    have hp := (hpair i j).1
    simpa [IsSign, Matrix.add_apply, Matrix.one_apply_ne hij] using hp
  have hrow : ∀ i, ∑ j, D₁ i j = 0 := by
    intro i
    have h₁ := congrFun (congrFun hprod (Sum.inl (Sum.inr i)))
      (Sum.inl (Sum.inl 0))
    have h₂ := congrFun (congrFun hprod (Sum.inl (Sum.inr i)))
      (Sum.inr (Sum.inl 0))
    simp only [c2Display, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.zero_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Fin.sum_univ_one, mul_one, mul_zero, mul_neg,
      zero_add, Finset.sum_neg_distrib, reduceCtorEq,
      Sum.inl.injEq, if_false] at h₁ h₂
    linarith [h₁, h₂]
  exact no_handshake_matrix m hm0 hm ⟨D₁, hsymm, hdiag, hoff, hrow⟩

end HadamardFormalCore
