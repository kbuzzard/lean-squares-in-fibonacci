import definitions
import fib_mod
import data.int.modeq

lemma luc_odd_of_not_3_div (n : ℕ) : luc (3 * n + 1) % 2 = 1 ∧
luc (3 * n + 2) % 2 = 1 :=
begin
  split,
  { rw ←luc_mod_eq,
    rw luc_mod_2,
    simp,refl,
  },
  { rw ←luc_mod_eq,
    rw luc_mod_2,
    simp,refl,
  }
end
--Prove that v m is not a multiple of 3 if 4 divides m.
lemma luc_coprime_to_3_of_4_div (n : ℕ) : luc (4 * n) % 3 ≠ 0 :=
begin
  rw ←luc_mod_eq,
  rw luc_mod_3,
  -- cases n even or odd
  --case on  (n % 2 = 1)
  suffices H : n % 2 = 0 ∨ n % 2 = 1,
  cases H,
  { -- n % 2 = 0
    suffices H2 : 4 * n % 8 = 0,
      rw H2,
      exact dec_trivial,
      change n ≡ 0 [MOD 2] at H,
      show 4 * n ≡ 0 [MOD 8],
      have a : 2∣n, from nat.modeq.modeq_zero_iff.1 H,
      rw nat.modeq.modeq_zero_iff,
      change 4*2 ∣ 4 * n,
      have q : 4 > 0, by norm_num,
      rw nat.mul_dvd_mul_iff_left q,
      exact a,
  },
  {
  suffices H1: 4 * n % 8 = 4,
  rw H1,
  exact dec_trivial,
  have h2 := nat.mod_add_div n 2,
  rw H at h2,
  rw [←h2,mul_add,←mul_assoc],
  show (4 + 8 * _) % 8 = 4,
  rw nat.add_mul_mod_self_left,
  exact dec_trivial,
  },
  generalize H: n % 2 = k,
   have q2: k < 2,
  {
    have q3: 2 > 0, from dec_trivial,
    have q4 : n % 2 < 2, from nat.mod_lt n q3,
    rw H at q4,
    exact q4,
  },
  {
    clear H,
    revert q2 k,
    exact dec_trivial,
  },

end
/-
#check nat.mul_dvd_mul_iff_left
#check int.coe_nat_dvd
-/
--n : ℕ,
--H : n % 2 = 0
--⊢ 4 * n % 8 = 0

--#check nat.mod

--Prove that v m ≡ 7 mod 8 if m ≡ 4 mod 12 or m ≡ 8 mod 12.
