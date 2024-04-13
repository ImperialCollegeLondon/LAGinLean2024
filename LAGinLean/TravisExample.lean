/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

-- import the theory of linear independence
import Mathlib

-- Let K be a field
variable (K : Type) [Field K]

-- Let V be a finite-dimensional vector space over K
variable (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

-- Lean's definition of linear independence works with indexed lists (which can have repeated
-- elements) rather than sets

-- Let `ι` be a finite indexing set and say `xᵢ` for `i ∈ ι` are linearly independent
variable {ι : Type} [Finite ι] (x : ι → V) (hx : LinearIndependent K x)

-- Let `S` be a finite subset of `V` and assume `S` spans
variable {S : Set V} (hS : S.Finite) (hSspan : Submodule.span K S = ⊤)

-- Then `#ι ≤ #S`

/-- A linearly independent set has cardinality less than or equal to that of any spanning set.
-/
theorem linearIndependent_card_le_span_card : Nat.card ι ≤ S.ncard := by

  sorry
