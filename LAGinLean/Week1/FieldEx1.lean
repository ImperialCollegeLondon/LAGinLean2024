import Mathlib.Tactic

variable (p : ℕ) [hp : Fact p.Prime]

@[ext]
structure F where
  val : ℕ
  cond : val < p
  deriving DecidableEq

variable {p}

namespace F

-- ignore this proof
instance : Finite (F p) := .intro ⟨fun x ↦ ⟨x.1, x.2⟩, fun x ↦ ⟨x.1, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance : Zero (F p) where
  zero := ⟨0, hp.out.pos⟩

instance : One (F p) where
  one := ⟨1, hp.out.one_lt⟩

instance : Add (F p) where
  add x y := ⟨(x.val + y.val) % p, Nat.mod_lt _ hp.out.pos⟩

instance : Mul (F p) where
  mul x y := ⟨(x.val * y.val) % p, Nat.mod_lt _ hp.out.pos⟩

instance : Neg (F p) where
  neg x := ⟨(p - x.val) % p, Nat.mod_lt _ hp.out.pos⟩

/-- Additive axioms -/

lemma add_comm (a b : F p) : a + b = b + a := by
  ext
  calc  (a + b).val
    _ = (a.val + b.val) % p := rfl
    _ = (b.val + a.val) % p := by rw?
    _ = (b + a).val         := rfl

lemma zero_add (a : F p) : 0 + a = a := by
  have : a.val < p := a.cond
  ext
  calc  (0 + a).val
    _ = (0 + a.val) % p := rfl
    _ = a.val % p       := by rw?
    _ = a.val           := by rw?

lemma add_zero (a : F p) : a + 0 = a := by
  rw [add_comm, zero_add]

lemma add_assoc (a b c : F p) : (a + b) + c = a + (b + c) := by
  sorry

lemma add_left_neg (a : F p) : -a + a = 0 := by
  have := a.cond.le
  sorry

/-- Multiplicative axioms -/

lemma mul_comm (a b : F p) : a * b = b * a := by
  ext
  sorry

lemma zero_mul (a : F p) : 0 * a = 0 := by
  ext
  sorry

lemma mul_zero (a : F p) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

lemma one_mul (a : F p) : 1 * a = a := by
  have : a.val < p := a.cond
  sorry

lemma mul_one (a : F p) : a * 1 = a := by
  rw [mul_comm, one_mul]

lemma mul_assoc (a b c : F p) : (a * b) * c = a * (b * c) := by
  sorry

/-- Distributivity axioms -/

lemma left_distrib (a b c : F p) : a * (b + c) = a * b + a * c := by
  sorry

lemma right_distrib (a b c : F p) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm b, mul_comm]

/-
This is the hard part, both mathematically and lean-wise.

Here I have listed some lemmas that you may or may not need.
-/

#check Nat.dvd_of_mod_eq_zero
#check Nat.Prime.dvd_mul
#check Nat.eq_zero_of_dvd_of_lt
#check Finite.injective_iff_surjective

lemma invertibility (a : F p) (ha : a ≠ 0) : ∃ b : F p, a * b = 1 := by
  have hp : p.Prime := hp.out
  have hint₁ : ∀ x, a * x = 0 → x = 0 := by
    intro x hx
    sorry
  have hint₂ : Function.Injective (a * ·) := by
    intro x y (e : a * x = a * y)
    sorry
  have hint₃ : Function.Surjective (a * ·) := by
    sorry
  have hint₄ : ∀ b, ∃ c, a * c = b := hint₃
  sorry

/-- Put it all together -/

noncomputable
instance : Field (F p) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zsmul := zsmulRec
  add_left_neg := add_left_neg
  mul_comm := mul_comm
  inv a := if h : a = 0 then 0 else (invertibility a h).choose
  exists_pair_ne := ⟨0, 1, fun e ↦ by cases congr($e.1)⟩
  mul_inv_cancel a h := show a * dite _ _ _ = 1 from dif_neg h ▸ (invertibility a h).choose_spec
  inv_zero := dif_pos rfl
  qsmul := qsmulRec _

end F
