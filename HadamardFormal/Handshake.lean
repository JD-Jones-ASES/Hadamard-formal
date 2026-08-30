/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# The handshake parity obstruction

An odd-order symmetric integer matrix with zero diagonal, off-diagonal
entries in `{+1, -1}`, and zero row sums has order congruent to `1`
modulo `4`.
-/

namespace HadamardFormalCore

/-- A symmetric sign matrix with zero diagonal and zero row sums has order
congruent to one modulo four.  This is the handshake obstruction from
Hadamard-M, stated independently of its source-paper application. -/
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

end HadamardFormalCore
