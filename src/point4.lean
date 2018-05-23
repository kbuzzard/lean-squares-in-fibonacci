import definitions
import data.nat.gcd
import data.nat.prime

local attribute [elab_as_eliminator] nat.strong_induction_on

lemma luc_fib (m : ℕ) : luc (m + 3) = 2 * fib (m + 3) + fib m :=
nat.rec_on_two m rfl rfl $ λ n ih1 ih2,
show (luc (n + 3) + luc (nat.succ n + 3)) = 2 * (fib (n + 3) + fib (n + 4)) + (fib n + fib (n + 1)),
by rw [ih1, ih2, mul_add]; simp

open nat

lemma nat.gcd_add (a b : ℕ) : gcd (a + b) b = gcd a b :=
by rw [gcd_comm, gcd_rec, add_mod_right, ← gcd_rec, gcd_comm]

lemma nat.gcd_add_mul (a n b : ℕ) : gcd (a + n * b) b = gcd a b :=
by rw [gcd_comm, gcd_rec, add_mul_mod_self_right, ← gcd_rec, gcd_comm]

lemma fib_succ_coprime (m : ℕ) : coprime (fib (m + 1)) (fib m) :=
nat.rec_on m dec_trivial $ λ n ih,
show gcd (fib n + fib (n+1)) (fib (n+1)) = 1,
by rw [nat.gcd_add, gcd_comm, coprime.gcd_eq_one ih]

lemma gcd_fib_luc_dvd_two (m : ℕ) : gcd (fib m) (luc m) ∣ 2 :=
nat.cases_on m dec_trivial $ λ n, nat.cases_on n dec_trivial $
λ n, nat.cases_on n dec_trivial $ λ n,
show gcd (fib (n+3)) (luc (n+3)) ∣ 2,
by rw [luc_fib, gcd_comm, add_comm, nat.gcd_add_mul];
change gcd (fib n) (fib (n+1) + (fib n + fib (n+1))) ∣ 2;
rw [gcd_comm, add_left_comm, add_comm, nat.gcd_add, ← mul_two];
rw [coprime.gcd_mul_left_cancel 2 (fib_succ_coprime n)];
apply gcd_dvd_left

-- Prime trick thanks to Chris and Mario.
lemma gcd_fib_luc_one_or_two (m : ℕ) : gcd (fib m) (luc m) = 1 ∨ gcd (fib m) (luc m) = 2 :=
(dvd_prime prime_two).1 $ gcd_fib_luc_dvd_two m