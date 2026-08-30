/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import HadamardFormal.Defs
import HadamardFormal.Data.Generated

/-!
# Kernel-checked finite inputs

The literals in `HadamardFormal.Data.Generated` are emitted by the committed
hash-checking exporter.  This module checks the mathematical T-matrix and
Williamson predicates with ordinary kernel reduction.  No large Hadamard
matrix is materialized here.
-/

namespace HadamardFormalCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-103 data satisfy the periodic T-matrix axiom. -/
theorem t103_isTMatrix : IsTMatrixQuadruple HadamardFormal.Data.t103 := by
  exact HadamardFormal.Data.t103_isTMatrixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-163 data satisfy the periodic T-matrix axiom. -/
theorem t163_isTMatrix : IsTMatrixQuadruple HadamardFormal.Data.t163 := by
  exact HadamardFormal.Data.t163_isTMatrixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-7 data form a Williamson quadruple. -/
theorem w7_isWilliamson : IsWilliamson HadamardFormal.Data.w7 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-11 data form a Williamson quadruple. -/
theorem w11_isWilliamson : IsWilliamson HadamardFormal.Data.w11 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-13 data form a Williamson quadruple. -/
theorem w13_isWilliamson : IsWilliamson HadamardFormal.Data.w13 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-17 data form a Williamson quadruple. -/
theorem w17_isWilliamson : IsWilliamson HadamardFormal.Data.w17 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-19 data form a Williamson quadruple. -/
theorem w19_isWilliamson : IsWilliamson HadamardFormal.Data.w19 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-23 data form a Williamson quadruple. -/
theorem w23_isWilliamson : IsWilliamson HadamardFormal.Data.w23 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of a fixed-length integer autocorrelation sum
-- needs unbounded heartbeats; the bump is scoped to this one check.
/-- The generated order-29 data form a Williamson quadruple. -/
theorem w29_isWilliamson : IsWilliamson HadamardFormal.Data.w29 := by
  decide

end HadamardFormalCore
