import HadamardFormal

/-!
# Hadamard formalization solution

This module exposes exactly the public challenge statements under the Palomar
namespace and discharges them through the internal, provenance-tracked
formalization.
-/

namespace HadamardFormal

open scoped BigOperators

def IsSign (z : ℤ) : Prop :=
  z = 1 ∨ z = -1

abbrev Sequence (n : ℕ) := Fin n → ℤ

abbrev Quadruple (n : ℕ) := Fin 4 → Sequence n

def paf {n : ℕ} [NeZero n] (x : Sequence n) (s : Fin n) : ℤ :=
  ∑ q, x q * x (q + s)

def deltaZero {n : ℕ} [NeZero n] (s : Fin n) : ℤ :=
  if s = 0 then 1 else 0

def IsTEntry (z : ℤ) : Prop :=
  z = 0 ∨ IsSign z

def supportCount {n : ℕ} (T : Quadruple n) (q : Fin n) : ℕ :=
  (Finset.univ.filter fun i ↦ T i q ≠ 0).card

def IsTMatrixQuadruple {n : ℕ} [NeZero n] (T : Quadruple n) : Prop :=
  (∀ i q, IsTEntry (T i q)) ∧
    (∀ q, supportCount T q = 1) ∧
      ∀ s, ∑ i, paf (T i) s = (n : ℤ) * deltaZero s

def IsSymmetricSequence {n : ℕ} [NeZero n] (x : Sequence n) : Prop :=
  ∀ q, x (-q) = x q

def IsWilliamson {n : ℕ} [NeZero n] (W : Quadruple n) : Prop :=
  (∀ i q, IsSign (W i q)) ∧
    (∀ i, IsSymmetricSequence (W i)) ∧
      ∀ s, ∑ i, paf (W i) s = 4 * (n : ℤ) * deltaZero s

def HadamardExists (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard

theorem handshake_mod_four
    (m : ℕ)
    (hm : Odd m)
    (D : Matrix (Fin m) (Fin m) ℤ)
    (hsymm : D.transpose = D)
    (hdiag : ∀ i, D i i = 0)
    (hoff : ∀ i j, i ≠ j → D i j = 1 ∨ D i j = -1)
    (hrow : ∀ i, ∑ j, D i j = 0) :
    m % 4 = 1 := by
  exact HadamardFormalCore.handshake_mod_four m hm D hsymm hdiag hoff hrow

theorem cooperWallis {t w : ℕ} [NeZero t] [NeZero w]
    {T : Quadruple t} {W : Quadruple w}
    (hT : IsTMatrixQuadruple T) (hW : IsWilliamson W) :
    HadamardExists (4 * t * w) := by
  have hTCore : HadamardFormalCore.IsTMatrixQuadruple T := by
    simpa only [IsTMatrixQuadruple, HadamardFormalCore.IsTMatrixQuadruple,
      IsTEntry, HadamardFormalCore.IsTEntry, IsSign, HadamardFormalCore.IsSign,
      supportCount, HadamardFormalCore.supportCount, paf, HadamardFormalCore.paf,
      deltaZero, HadamardFormalCore.deltaZero] using hT
  have hWCore : HadamardFormalCore.IsWilliamson W := by
    simpa only [IsWilliamson, HadamardFormalCore.IsWilliamson,
      IsSymmetricSequence, HadamardFormalCore.IsSymmetricSequence,
      IsSign, HadamardFormalCore.IsSign, paf, HadamardFormalCore.paf,
      deltaZero, HadamardFormalCore.deltaZero] using hW
  change HadamardFormalCore.HadamardExists (4 * t * w)
  exact HadamardFormalCore.cooperWallis hTCore hWCore

theorem hadamard_7172 : HadamardExists 7172 := by
  change HadamardFormalCore.HadamardExists 7172
  exact HadamardFormalCore.hadamard_7172

theorem hadamard_8476 : HadamardExists 8476 := by
  change HadamardFormalCore.HadamardExists 8476
  exact HadamardFormalCore.hadamard_8476

theorem hadamard_2884 : HadamardExists 2884 := by
  change HadamardFormalCore.HadamardExists 2884
  exact HadamardFormalCore.hadamard_2884

theorem hadamard_4532 : HadamardExists 4532 := by
  change HadamardFormalCore.HadamardExists 4532
  exact HadamardFormalCore.hadamard_4532

theorem hadamard_7004 : HadamardExists 7004 := by
  change HadamardFormalCore.HadamardExists 7004
  exact HadamardFormalCore.hadamard_7004

theorem hadamard_7828 : HadamardExists 7828 := by
  change HadamardFormalCore.HadamardExists 7828
  exact HadamardFormalCore.hadamard_7828

theorem hadamard_9476 : HadamardExists 9476 := by
  change HadamardFormalCore.HadamardExists 9476
  exact HadamardFormalCore.hadamard_9476

theorem hadamard_11948 : HadamardExists 11948 := by
  change HadamardFormalCore.HadamardExists 11948
  exact HadamardFormalCore.hadamard_11948

end HadamardFormal
