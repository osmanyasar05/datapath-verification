import Blase

/-!
  This file proves the correctness of a carry-save adder (CSA) in Lean 4.
-/

namespace CSA

-- The result of a carry-save adder consists of a partial sum `s` and carry bits `t`.
structure CSAResult (w : ℕ) where
  s : BitVec w
  t : BitVec w

-- The carry-save adder splits the sum into a partial sum `s` and
-- carry bits `t`, such that the original sum is recovered by
-- adding `s` to the carries shifted left by 1 (i.e., t * 2).
def carrySave (w : ℕ) (a b c : BitVec w) : CSAResult w :=
  let s := a ^^^ b ^^^ c
  let t := (a &&& b ||| a &&& c ||| b &&& c)
  ⟨s, t⟩

#eval carrySave 4 5 5 5

-- a + b + c = CSA(a, b, c)
theorem carrySaveAdder (w : ℕ) (a b c : BitVec w) :
    let ⟨s, t⟩ := carrySave w a b c
    a + b + c = s + t <<< 1 := by
    simp [carrySave]
    bv_automata_classic

-- a + b + c + d = CSA(CSA(a, b, c), d)
theorem carrySaveAdder4Input (w : ℕ) (a b c d : BitVec w) :
    let ⟨s1, t1⟩ := carrySave w a b c
    let ⟨s2, t2⟩ := carrySave w s1 (t1 <<< 1) d
    a + b + c + d = s2 + t2 <<< 1 := by
    simp [carrySave]
    bv_automata_classic

-- CSA(CSA(p1, p2, p3), p4), with p1, p2, p3, p4 being the partial products of a 4-bit multiplication.
def mul4 (a b : BitVec 4) : BitVec 4 :=
  -- partial products
  let p0 : BitVec 4 := (BitVec.ofBool a[0]).zeroExtend 4 * b
  let p1 : BitVec 4 := ((BitVec.ofBool a[1]).zeroExtend 4 * b) <<< 1
  let p2 : BitVec 4 := ((BitVec.ofBool a[2]).zeroExtend 4 * b) <<< 2
  let p3 : BitVec 4 := ((BitVec.ofBool a[3]).zeroExtend 4 * b) <<< 3
  -- sum partial products
  let ⟨s1, t1⟩ := carrySave 4 p0 p1 p2
  let ⟨s2, t2⟩ := carrySave 4 s1 (t1 <<< 1) p3
  s2 + (t2 <<< 1)

#eval mul4 4 3

-- a*b = (a[0] * b) + (2 * a[1] * b) + (4 * a[2] * b) + (8 * a[3] * b)
@[simp]
theorem mul4_partial_products (a b : BitVec 4) :
    let p0 : BitVec 4 := (BitVec.ofBool a[0]).zeroExtend 4 * b
    let p1 : BitVec 4 := ((BitVec.ofBool a[1]).zeroExtend 4 * b) <<< 1
    let p2 : BitVec 4 := ((BitVec.ofBool a[2]).zeroExtend 4 * b) <<< 2
    let p3 : BitVec 4 := ((BitVec.ofBool a[3]).zeroExtend 4 * b) <<< 3
    a * b = p0 + p1 + p2 + p3 := by
    bv_decide

-- a * b = CSA(CSA(p0, p1, p2), p3)
theorem mul4_correct (a b : BitVec 4) : a * b = mul4 a b := by
  rw [mul4_partial_products]
  simp only [mul4, carrySave]
  bv_decide

-- N:2 compressor implementation.
-- Takes a vector of n bit-vectors and reduces them to 2 bit-vectors (sum and carry) using a tree of carry-save adders.
def chain {w n : Nat} (v : Vector (BitVec w) n) : CSAResult w :=
  match n with
  | 0 => ⟨0, 0⟩
  | 1 => ⟨v[0], 0⟩
  | 2 => carrySave w v[0] v[1] 0
  | 3 => carrySave w v[0] v[1] v[2]
  | n + 1 =>
    let ⟨sum, carry⟩ := chain (v.take n) -- takes the first n elements of the vector.
    let ⟨s, t⟩ := carrySave w sum (carry <<< 1) (v.back) -- the chained carry is shifted left by 1 to align with the next input.
    ⟨s, t⟩ -- return the carry without shifting, the next level handles it.

#eval chain (v := (⟨#[5, 2, 3, 7, 3], rfl⟩ : Vector (BitVec 32) 5))

theorem chain_correct {w n : Nat} (v : Vector (BitVec w) n) :
  let ⟨s, t⟩ := chain v
  s + t <<< 1 = v.sum := by
  sorry

end CSA
