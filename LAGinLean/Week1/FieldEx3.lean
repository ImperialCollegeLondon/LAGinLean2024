import Mathlib

@[ext]
structure F where
  a : ZMod 3
  b : ZMod 3
  deriving DecidableEq

instance : Add F where
  add x y := ⟨x.a + y.a, x.b + y.b⟩

instance : Mul F where
  mul x y := ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a⟩

instance : Zero F where
  zero := ⟨0, 0⟩

instance : One F where
  one := ⟨1, 0⟩

instance : Neg F where
  neg x := ⟨-x.a, -x.b⟩

namespace F

/-- Additive axioms -/

lemma add_comm (a b : F) : a + b = b + a := by
  ext
  · calc (a + b).a
      _  = a.a + b.a := rfl
      _  = b.a + a.a := by rw? says rw [@_root_.add_comm]
      _  = (b + a).a := rfl
  · calc (a + b).b
      _  = a.b + b.b := rfl
      _  = b.b + a.b := by rw? says rw [@_root_.add_comm]
      _  = (b + a).b := rfl

lemma zero_add (a : F) : 0 + a = a := by
  sorry

lemma add_assoc (a b c : F) : (a + b) + c = a + (b + c) := by
  sorry

lemma add_left_neg (a : F) : -a + a = 0 := by
  sorry

/-- Multiplicative axioms -/

lemma mul_comm (a b : F) : a * b = b * a := by
  sorry

lemma zero_mul (a : F) : 0 * a = 0 := by
  sorry

lemma one_mul (a : F) : 1 * a = a := by
  sorry

lemma mul_assoc (a b c : F) : (a * b) * c = a * (b * c) := by
  sorry

lemma left_distrib (a b c : F) : a * (b + c) = a * b + a * c := by
  sorry

lemma invertibility (a : F) (ha : a ≠ 0) : ∃ b : F, a * b = 1 := by
  use ⟨sorry, sorry⟩ -- your `b`
  sorry

/-- Put it all together -/

noncomputable
instance : Field F where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero _ := by rw [add_comm, zero_add]
  nsmul := nsmulRec
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib _ b _ := by rw [mul_comm, left_distrib, mul_comm b, mul_comm]
  zero_mul := zero_mul
  mul_zero _ := by rw [mul_comm, zero_mul]
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one _ := by rw [mul_comm, one_mul]
  zsmul := zsmulRec
  add_left_neg := add_left_neg
  mul_comm := mul_comm
  inv a := if h : a = 0 then 0 else (invertibility a h).choose
  exists_pair_ne := ⟨0, 1, fun e ↦ by cases congr($e.1)⟩
  mul_inv_cancel a h := show a * dite _ _ _ = 1 from dif_neg h ▸ (invertibility a h).choose_spec
  inv_zero := dif_pos rfl
  qsmul := qsmulRec _

end F
