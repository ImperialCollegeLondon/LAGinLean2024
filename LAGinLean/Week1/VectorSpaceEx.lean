import Mathlib

variable (F) [Field F] (n : Type*)

def Fn := n → F

namespace Fn

@[ext] lemma ext (a b : Fn F n) (e : ∀ i, a i = b i) : a = b := funext e

instance : Add (Fn F n) where
  add a b i := a i + b i -- the i-th component of a + b is a i + b i

instance : Neg (Fn F n) where
  neg a i := - a i

instance : Zero (Fn F n) where
  zero _ := 0

instance : SMul F (Fn F n) where
  smul k a i := k * a i -- the i-th component of k • a is k * a i

variable {F n}

lemma add_comm (a b : Fn F n) : a + b = b + a := by
  ext i
  calc  (a + b) i
    _ = a i + b i := rfl
    _ = b i + a i := by rw?
    _ = (b + a) i := rfl

lemma zero_add (a : Fn F n) : 0 + a = a := by
  sorry

lemma add_zero (a : Fn F n) : a + 0 = a := by
  rw [add_comm, zero_add]

lemma add_assoc (a b c : Fn F n) : (a + b) + c = a + (b + c) := by
  sorry

lemma add_left_neg (a : Fn F n) : -a + a = 0 := by
  sorry

instance : AddCommGroup (Fn F n) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_left_neg := add_left_neg
  add_comm := add_comm

lemma smul_add (k : F) (a b : Fn F n) : k • (a + b) = k • a + k • b := by
  sorry

lemma add_smul (k l : F) (a : Fn F n) : (k + l) • a = k • a + l • a := by
  sorry

lemma mul_smul (k l : F) (a : Fn F n) : (k * l) • a = k • l • a := by
  sorry

lemma one_smul (a : Fn F n) : (1 : F) • a = a := by
  sorry

lemma zero_smul (a : Fn F n) : (0 : F) • a = 0 := by
  sorry

lemma smul_zero (k : F) : k • (0 : Fn F n) = 0 := by
  sorry

-- Note: module means vector space
instance : Module F (Fn F n) where
  one_smul := one_smul
  mul_smul := mul_smul
  smul_zero := smul_zero
  smul_add := smul_add
  add_smul := add_smul
  zero_smul := zero_smul

end Fn
