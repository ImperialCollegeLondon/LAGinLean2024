import Mathlib

open Complex(I)

def QI : Set ℂ := { a + b * I | (a : ℚ) (b : ℚ) }

local notation "ℚ[I]" => QI

lemma mem_QI_iff {x} : x ∈ ℚ[I] ↔ ∃ a b : ℚ, a + b * I = x := Iff.rfl

namespace QI

-- Example
lemma add_mem {x y : ℂ} (hx : x ∈ ℚ[I]) (hy : y ∈ ℚ[I]) : x + y ∈ ℚ[I] := by
  obtain ⟨xa, xb, rfl⟩ := hx -- magic syntax to subtitute `x` with `xa + xb * I` if `x ∈ ℚ[I]`).
  obtain ⟨ya, yb, rfl⟩ := hy -- magic syntax to subtitute `y` with `ya + yb * I` if `x ∈ ℚ[I]`).
  have : (xa + xb * I) + (ya + yb * I) = (xa + ya) + (xb + yb) * I
  · ring
  rw [this]
  use (xa + ya)
  use (xb + yb)
  norm_num

lemma zero_mem : 0 ∈ ℚ[I] := by
  sorry

lemma neg_mem {x : ℂ} (hx : x ∈ ℚ[I]) : -x ∈ ℚ[I] := by
  sorry

lemma mul_mem {x y : ℂ} (hx : x ∈ ℚ[I]) (hy : y ∈ ℚ[I]) : x * y ∈ ℚ[I] := by
  obtain ⟨xa, xb, rfl⟩ := hx
  obtain ⟨ya, yb, rfl⟩ := hy
  sorry

lemma one_mem : 1 ∈ ℚ[I] := by
  sorry

lemma inv_mem {x : ℂ} (hx : x ∈ ℚ[I]) (hx' : x ≠ 0) : x⁻¹ ∈ ℚ[I] := by
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
