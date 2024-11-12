/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

-- import the theory of finite-dimensional vector spaces
import Mathlib.LinearAlgebra.FiniteDimensional
-- import the theory of the size of finite sets.
import Mathlib.Data.Set.Card

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

/-

Travis' suggested proof:

Let S be a linearly independent set and T a finite spanning set for a vector space V.

Proposition 1: |T| >= |S|.

Lemma 1: Subsets of linearly independent sets are linearly independent.

Proof: Any linear dependence on the subset produces a linear dependence on the whole set.

Proof of Proposition 1: By contradiction, we can suppose that |S|>|T|. By the lemma it's enough to assume that |S|=|T|+1, in particular |S| finite.  Now the result follows from the following stronger fact:

Proposition 2: Let S be a finite linearly independent set and T a finite spanning set.  Then there exists a spanning set T' with |T'|=|T| and T \supseteq S.

Proof: We induct on |S\T|.  The base case of zero is trivial.  Now suppose that s is in S\T.  Since T spans, we can write s = a_1 t_1 + ... + a_m t_m = s for t_i in T. Since S is linearly independent, we must have some t_i not in S and a_i nonzero. Without loss of generality suppose i=1. Write

t_1 = a_1^{-1} (-a_2 t_2 - ... - a_m t_m + s).

Therefore, t_1 is in the span of T'=(T \cup {s}) \ {t_1}.  Since s \notin T, we have |T'|=|T|.  Since t_1 and T \ {t_1} are in the span of T', T is in the span of T', and hence T' spans V.  Since t_1 was not in S, we have S\T' = (S\T)\{s}, hence |S\T'| = |S\T|-1. By the inductive hypothesis we can replace T' with a spanning set T'' containing S. QED
-/
