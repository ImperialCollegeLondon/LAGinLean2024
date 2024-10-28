import Mathlib

open Complex(I)

def QI : Set ℂ := { a + b * I | (a : ℚ) (b : ℚ) }

local notation "ℚ[I]" => QI

namespace QI

/-
General hint: `simp` and `norm_num` are powerful tactics
that can help simplify and organise the equation.

If
```
simp
ring_nf
```
doesn't solve the problem, try
```
simp
ring_nf
simp
ring_nf
simp
ring_nf
```
until it does.

-/

-- Example
lemma add_mem {x y : ℂ} (hx : x ∈ ℚ[I]) (hy : y ∈ ℚ[I]) : x + y ∈ ℚ[I] := by
  obtain ⟨xa, xb, rfl⟩ := hx -- magic syntax to subtitute `x` with `xa + xb * I` if `x ∈ ℚ[I]`).
  obtain ⟨ya, yb, rfl⟩ := hy -- magic syntax to subtitute `y` with `ya + yb * I` if `x ∈ ℚ[I]`).
  use xa + ya, xb + yb       -- use `a := xa + ya` and `b := xb + yb` in `a + b * I = x + y`.
  simp                       -- simplify terms
  ring_nf                    -- organise terms

lemma zero_mem : 0 ∈ ℚ[I] := by
  use sorry, sorry
  sorry

lemma neg_mem {x : ℂ} (hx : x ∈ ℚ[I]) : -x ∈ ℚ[I] := by
  obtain ⟨xa, xb, rfl⟩ := hx
  sorry


lemma mul_mem {x y : ℂ} (hx : x ∈ ℚ[I]) (hy : y ∈ ℚ[I]) : x * y ∈ ℚ[I] := by
  sorry


lemma one_mem : 1 ∈ ℚ[I] := by
  sorry

lemma inv_mem {x : ℂ} (hx : x ∈ ℚ[I]) (hx' : x ≠ 0) : x⁻¹ ∈ ℚ[I] := by
  obtain ⟨xa, xb, rfl⟩ := hx
  /- You can have this one for free :) -/
  have hint₁ : xa + -xb * I ≠ 0 := fun e ↦ by
    simp [show xa = 0 by simpa using congr(($e).re),
      show xb = 0 by simpa using congr(($e).im)] at hx'
  have hint₂ : xa ^ 2 + xb ^ 2 = (xa + xb * I) * (xa + -xb * I) := by
    sorry
  sorry

noncomputable
def QI_subfield : Subfield ℂ where
  carrier := QI
  mul_mem' := mul_mem
  one_mem' := one_mem
  zero_mem' := zero_mem
  neg_mem' := neg_mem
  add_mem' := add_mem
  inv_mem' x hx := if h : x = 0 then
    h ▸ (inv_zero (G₀ := ℂ)).symm ▸ zero_mem else inv_mem hx h

end QI
