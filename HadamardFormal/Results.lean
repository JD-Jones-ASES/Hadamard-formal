/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import HadamardFormal.CooperWallis
import HadamardFormal.Data

/-!
# First-tranche Hadamard orders

These theorems combine the kernel-checked T-matrix and Williamson witnesses
with the symbolic Cooper--Wallis/Goethals--Seidel construction.  The proof
terms do not materialize the resulting Hadamard matrices.
-/

namespace HadamardFormalCore

/-- The order-163 T-matrix and order-11 Williamson witnesses give order 7172. -/
theorem hadamard_7172 : HadamardExists 7172 := by
  simpa using cooperWallis t163_isTMatrix w11_isWilliamson

/-- The order-163 T-matrix and order-13 Williamson witnesses give order 8476. -/
theorem hadamard_8476 : HadamardExists 8476 := by
  simpa using cooperWallis t163_isTMatrix w13_isWilliamson

/-- The order-103 T-matrix and order-7 Williamson witnesses give order 2884. -/
theorem hadamard_2884 : HadamardExists 2884 := by
  simpa using cooperWallis t103_isTMatrix w7_isWilliamson

/-- The order-103 T-matrix and order-11 Williamson witnesses give order 4532. -/
theorem hadamard_4532 : HadamardExists 4532 := by
  simpa using cooperWallis t103_isTMatrix w11_isWilliamson

/-- The order-103 T-matrix and order-17 Williamson witnesses give order 7004. -/
theorem hadamard_7004 : HadamardExists 7004 := by
  simpa using cooperWallis t103_isTMatrix w17_isWilliamson

/-- The order-103 T-matrix and order-19 Williamson witnesses give order 7828. -/
theorem hadamard_7828 : HadamardExists 7828 := by
  simpa using cooperWallis t103_isTMatrix w19_isWilliamson

/-- The order-103 T-matrix and order-23 Williamson witnesses give order 9476. -/
theorem hadamard_9476 : HadamardExists 9476 := by
  simpa using cooperWallis t103_isTMatrix w23_isWilliamson

/-- The order-103 T-matrix and order-29 Williamson witnesses give order 11948. -/
theorem hadamard_11948 : HadamardExists 11948 := by
  simpa using cooperWallis t103_isTMatrix w29_isWilliamson

end HadamardFormalCore
