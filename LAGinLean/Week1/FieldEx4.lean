import Mathlib.Tactic

variable {p : ℕ} [hp : Fact p.Prime]

@[ext]
structure F2 (p : ℕ) [Fact p.Prime] : Type where
  a : ZMod p
  b : ZMod p
  deriving DecidableEq, Fintype

namespace F2

instance : Add (F2 p) where
  add x y := ⟨x.a + y.a, x.b + y.b⟩

instance : Zero (F2 p) where
  zero := ⟨0, 0⟩

instance : One (F2 p) where
  one := ⟨1, 0⟩

instance : Neg (F2 p) where
  neg x := ⟨-x.a, -x.b⟩

/-- All of this shows that `F2 p` is a commutative group. -/
instance : AddCommGroup (F2 p) where
  add_assoc a b c := F2.ext _ _ (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add a := F2.ext _ _ (zero_add _) (zero_add _)
  add_zero a := F2.ext _ _ (add_zero _) (add_zero _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_left_neg a := F2.ext _ _ (add_left_neg _) (add_left_neg _)
  add_comm a b := F2.ext _ _ (add_comm _ _) (add_comm _ _)

instance : Mul (F2 p) where
  mul x y := ⟨sorry, sorry⟩ -- Mathematical question: how do you define this?

lemma mul_comm (a b : F2 p) : a * b = b * a := by
  sorry

lemma zero_mul (a : F2 p) : 0 * a = 0 := by
  sorry

lemma mul_zero (a : F2 p) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

lemma one_mul (a : F2 p) : 1 * a = a := by
  sorry

lemma mul_one (a : F2 p) : a * 1 = a := by
  rw [mul_comm, one_mul]

lemma mul_assoc (a b c : F2 p) : (a * b) * c = a * (b * c) := by
  sorry

/-- Distributivity axioms -/

lemma left_distrib (a b c : F2 p) : a * (b + c) = a * b + a * c := by
  sorry

lemma right_distrib (a b c : F2 p) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm b, mul_comm]

lemma invertibility (a : F2 p) (ha : a ≠ 0) : ∃ b : F2 p, a * b = 1 := by
  sorry

noncomputable
instance : Field (F2 p) where
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
  exists_pair_ne := ⟨0, 1, fun e ↦ by have : NeZero p := ⟨hp.out.pos.ne'⟩
                                      simpa using show (0 : ZMod p) = 1 from congr($e.1)⟩
  mul_inv_cancel a h := show a * dite _ _ _ = 1 from dif_neg h ▸ (invertibility a h).choose_spec
  inv_zero := dif_pos rfl
  qsmul := qsmulRec _

-- F2 p has cardinality p ^ 2
lemma card_f2 : Nat.card (F2 p) = p ^ 2 := by
  rw [Nat.card_congr (β := ZMod p × ZMod p) ⟨fun a ↦ ⟨a.1, a.2⟩, fun a ↦ ⟨a.1, a.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩]
  simp [pow_two]
