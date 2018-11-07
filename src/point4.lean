import definitions
import point3
import data.nat.prime

open nat

/-- point 4, first part-/
lemma luc_fib (m : ℕ) : luc (m + 3) = 2 * fib (m + 3) + fib m :=
int.coe_nat_inj $ by rw [int.coe_nat_add, int.coe_nat_mul];
  rw [← fib_down, ← fib_down, ← luc_down, Luc, Fib, Fib];
  rw [α_Fib, α_Fib, β_Fib]; dsimp;
  rw [add_neg_cancel_right];
  repeat { rw Fib_add_one_add_one }; simp [add_mul]

lemma fib_succ_coprime (m : ℕ) : coprime (fib (m + 1)) (fib m) :=
nat.rec_on m dec_trivial $ λ n ih,
show gcd (fib n + fib (n+1)) (fib (n+1)) = 1,
by rw [nat.gcd_add, nat.gcd_comm, coprime.gcd_eq_one ih]

lemma gcd_fib_luc_dvd_two (m : ℕ) : gcd (fib m) (luc m) ∣ 2 :=
nat.cases_on m dec_trivial $ λ n, nat.cases_on n dec_trivial $
λ n, nat.cases_on n dec_trivial $ λ n,
show gcd (fib (n+3)) (luc (n+3)) ∣ 2,
by rw [luc_fib, nat.gcd_comm, add_comm, nat.gcd_add_mul_right];
change gcd (fib n) (fib (n+1) + (fib n + fib (n+1))) ∣ 2;
rw [nat.gcd_comm, add_left_comm, add_comm, nat.gcd_add, ← mul_two];
rw [coprime.gcd_mul_left_cancel 2 (fib_succ_coprime n)];
apply nat.gcd_dvd_left

-- Prime trick thanks to Chris and Mario.
/-- point 4, last part-/
lemma gcd_fib_luc_one_or_two (m : ℕ) : gcd (fib m) (luc m) = 1 ∨ gcd (fib m) (luc m) = 2 :=
(dvd_prime prime_two).1 $ gcd_fib_luc_dvd_two m

