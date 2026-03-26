import Blase
import DatapathVerification.ForLean

/-!
  This file proves the correctness of a carry-save adder (CSA) in Lean 4.
  Proof is based on: C. Berg, "Formal Verification of an IEEE Floating Point Adder", 2001.
  https://www.df7cb.de/cs/publications/2001/fpadder-cb.pdf
-/

namespace CSA

structure CSAResult (w : ℕ) where
  s : BitVec w
  t : BitVec (w + 1)

def carrySave : (w : ℕ) → BitVec w → BitVec w → BitVec w → CSAResult w
  | 0, _, _, _ => ⟨0#0, 0#1⟩
  | n + 1, a, b, c =>
    let aLo : BitVec n := a.truncate n
    let bLo : BitVec n := b.truncate n
    let cLo : BitVec n := c.truncate n
    let ⟨S, T⟩ := carrySave n aLo bLo cLo
    let aMsb := a[n]
    let bMsb := b[n]
    let cMsb := c[n]
    let x := aMsb ^^ bMsb
    let sum := x ^^ cMsb
    let carry := (aMsb && bMsb) || (aMsb && cMsb) || (bMsb && cMsb)
    ⟨BitVec.cons sum S, BitVec.cons carry T⟩

#eval carrySave 32 5 7 3

theorem carrySave_s_eq_xor (a b c : BitVec w) :
    (carrySave w a b c).s = a ^^^ b ^^^ c := by
  induction w with
  | zero => grind
  | succ n ih =>
    simp only [carrySave]
    rw [ih]
    grind

theorem carrySave_t_eq_shift (a b c : BitVec w) :
    (carrySave w a b c).t = (a &&& b ||| a &&& c ||| b &&& c).zeroExtend (w+1) <<< 1 := by
  induction w with
  | zero =>
    simp only [carrySave]
    bv_normalize
  | succ n ih =>
    simp only [carrySave]
    rw [ih]
    set x := a &&& b ||| a &&& c ||| b &&& c
    set trunc_and := BitVec.truncate n a &&& BitVec.truncate n b |||
               BitVec.truncate n a &&& BitVec.truncate n c |||
               BitVec.truncate n b &&& BitVec.truncate n c
    have hta : trunc_and = BitVec.truncate n x := by grind
    have hcarry : (a[n] && b[n] || c[n] && (a[n] ^^ b[n])) = x[n] := by grind
    rw [hta]
    ext i
    by_cases hi0 : i = 0
    · grind
    · by_cases hi : i = n + 1 <;> grind

theorem toNat_cons_eq_add_mul {a : BitVec w} {b : Bool} : (a.cons b).toNat = b.toNat * (2 ^ w) + a.toNat:= by
  cases b with
  | false => grind
  | true =>
    rw [BitVec.toNat_cons']
    simp
    omega

theorem fullAdder (a b c : Bool) :
  a.toNat + b.toNat + c.toNat =
  2 * ((a && b) || (c && (a ^^ b))).toNat + (a ^^ b ^^ c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

theorem toNat_toNat_truncate (a : BitVec w) (h: 1 ≤ w) : a.toNat = (a[w-1].toNat * (2 ^ (w - 1))) + (a.truncate (w - 1)).toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  simp [BitVec.toNat_eq_div_toNat a h]
  rw [Nat.div_add_mod']

theorem toNat_carrySave (a b c : BitVec w) :
    a.toNat + b.toNat + c.toNat =  ((carrySave w a b c).t).toNat + ((carrySave w a b c).s).toNat := by
  induction w with
  | zero => simp [carrySave]; grind
  | succ n ih =>
    simp only [carrySave]
    rw [toNat_toNat_truncate a (by omega), toNat_toNat_truncate b (by omega), toNat_toNat_truncate c (by omega)]
    simp only [toNat_cons_eq_add_mul]
    have ih_inst := ih (a.truncate n) (b.truncate n) (c.truncate n)
    simp only [Nat.add_one_sub_one]
    have := fullAdder a[n] b[n] c[n]
    ac_nf at *
    grind

theorem BitVec.zeroExtend_shiftLeft_toNat_eq (x : BitVec w) (h : x.msb = false) :
    (x.zeroExtend (w+1) <<< 1).toNat = (x <<< 1).toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, lt_add_iff_pos_right,
    zero_lt_one, BitVec.toNat_mod_cancel_of_lt]
  have : x.toNat <<< 1 < 2 ^ (w) := by
    have : x.toNat < 2 ^ (w - 1) := by grind
    rw [Nat.shiftLeft_eq]
    grind
  repeat rw [Nat.mod_eq_of_lt (by omega)]

theorem carrySave_t_eq_and_shift {a b c : BitVec w}
    (ha : a.msb = false) (hb : b.msb = false) (hc : c.msb = false) :
    (carrySave w a b c).t.toNat = ((a &&& b ||| a &&& c ||| b &&& c) <<< 1).toNat := by
  rw [carrySave_t_eq_shift a b c]
  set x := a &&& b ||| a &&& c ||| b &&& c with hx_def
  rw [BitVec.zeroExtend_shiftLeft_toNat_eq x (by grind)]


theorem add_add_eq
    (a b c : BitVec w)
    (ha : a.msb = false)
    (hb : b.msb = false)
    (hc : c.msb = false) :
    a + b + c = (a &&& b ||| a &&& c ||| b &&& c) <<< 1 + (a ^^^ b ^^^ c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, Nat.mod_add_mod]
  rw [toNat_carrySave, carrySave_t_eq_and_shift ha hb hc, carrySave_s_eq_xor]

theorem add_add_eq_bv_automata
    (a b c : BitVec w) :
    a + b + c = (a &&& b ||| a &&& c ||| b &&& c) <<< 1 + (a ^^^ b ^^^ c) := by
    bv_automata_classic

end CSA
