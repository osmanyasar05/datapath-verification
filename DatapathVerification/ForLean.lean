import Std.Tactic.BVDecide

theorem BitVec.eq_cons_truncate (a b c : BitVec (n + 1)) :
    a ^^^ b ^^^ c = BitVec.cons (a.msb ^^ b.msb ^^ c.msb)
                                (a.truncate n ^^^ b.truncate n ^^^ c.truncate n) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_cons]
  by_cases h : i = 0 <;> grind

theorem BitVec.toNat_eq_div_toNat (a : BitVec w) (h: 1 ≤ w) : a[w-1].toNat = a.toNat / 2 ^ (w - 1) := by
  simp only [Bool.toNat, BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
    Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero]
  have : a.toNat / 2 ^ (w - 1) % 2 = a.toNat / 2 ^ (w - 1) := by
      simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
      refine Nat.div_lt_of_lt_mul ?_
      have h1 : 2 ^ (w - 1) * 2 = 2 ^ w := by refine Nat.two_pow_pred_mul_two ?_; omega
      simp [h1]; omega
  by_cases h : a.toNat / 2 ^ (w - 1) % 2 == 1
  · simp only [h, cond_true]
    simp_all only [beq_iff_eq]
  · simp_all only [beq_iff_eq, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
    have : a.toNat / 2 ^ (w - 1) = 0 := by
      have h_nat : 0 ≤ a.toNat / 2 ^ (w - 1) := Nat.zero_le _
      omega
    simp [this]
