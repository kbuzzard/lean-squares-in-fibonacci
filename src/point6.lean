import definitions
import point3

-- 2F(m+n) = F(m) L(n) + L(m) F(n)
lemma two_mul_Fib_add (m n : ℤ) : 2 * Fib (m + n) = Fib m * Luc n + Luc m * Fib n :=
by rw [Fib, Fib, Fib, Luc, Luc, gpow_add, units.coe_mul, Zalpha.mul_r, two_mul];
  rw [α_Fib, α_Fib, β_Fib, β_Fib];
  have Hm := Fib_add_two (m-1);
  have Hn := Fib_add_two (n-1);
  rw [bit0, ← add_assoc, sub_add_cancel] at Hm Hn;
  simp [Hm, Hn, mul_add, add_mul]

lemma two_mul_fib_add (m n : ℕ) : 2 * fib (m + n) = fib m * luc n + luc m * fib n :=
int.coe_nat_inj $ by rw [int.coe_nat_add, int.coe_nat_mul, int.coe_nat_mul, int.coe_nat_mul];
  rw [← fib_down, ← fib_down, ← fib_down, ← luc_down, ← luc_down, ← two_mul_Fib_add]; refl

-- L(4n) + 2 = L(2n)^2
lemma Luc_four_mul (n : ℤ) : Luc (4 * n) = Luc (2 * n) * Luc (2 * n) - 2 :=
Zalpha.of_int_inj.1 $ by have := Luc_αβ; simp at this;
  simp [this, add_mul, mul_add];
  rw [← units.coe_mul, ← units.coe_mul, ← units.coe_mul, ← units.coe_mul];
  rw [← mul_gpow, ← mul_gpow, ← mul_gpow, ← mul_gpow]; simp;
  rw [gpow_mul (-1 : units ℤα)];
  have : (-1 : units ℤα)^(2:ℤ) = 1 := rfl;
  simp [this]; rw [bit0, add_mul, gpow_add, gpow_add, mul_gpow, mul_gpow]; ring

lemma luc_four_mul (n : ℕ) : luc (4 * n) + 2 = luc (2 * n) * luc (2 * n) :=
int.coe_nat_inj $ by simp; rw [← luc_down, ← luc_down];
  change 1 + (1 + Luc (4 * n)) = _; rw [Luc_four_mul]; ring

-- F(2n) = F(n) L(n)
lemma fib_two_mul (n : ℕ) : fib (2 * n) = fib n * luc n :=
nat.bit0_inj $ by rw [bit0, ← two_mul, two_mul n, two_mul_fib_add, mul_comm]; refl

-- L(2n) ∣ 2(F(m+4n) + F(m))
lemma luc_two_mul_dvd (m n : ℕ) : luc (2 * n) ∣ 2 * (fib (m + 4 * n) + fib m) :=
⟨luc (2 * n) * fib m + luc m * fib (2 * n),
by rw [mul_add, mul_add, two_mul_fib_add, mul_comm (fib m), add_right_comm, ← add_mul, luc_four_mul];
conv in (4 * n) { change ((2 * 2) * n) };
rw [mul_assoc 2, fib_two_mul]; ac_refl⟩

-- TODO: if ¬(3 ∣ n) then fib (m + 4*n) ≡ −fib m [MOD (luc (2*n))]