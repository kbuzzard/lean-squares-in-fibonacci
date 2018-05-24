import definitions
import data.nat.gcd
import mathlib_someday
import point4

theorem fib_add (m n : ℕ) : fib (m + n + 1) =
  fib m * fib n + fib (m + 1) * fib (n + 1) :=
nat.rec_on_two n (by unfold fib; rw [mul_zero, zero_add, mul_one]; refl)
  (by unfold fib; rw [zero_add, mul_one, mul_one]; refl) $ λ n ih1 ih2,
calc  fib (m + n + 1) + fib (m + nat.succ n + 1)
    = fib m * (fib n + fib (n+1)) + fib (m+1) * (fib (n+1) + (fib n + fib (n+1))) :
  by rw [ih1, ih2, fib, mul_add, mul_add, mul_add, mul_add, nat.succ_eq_add_one]; ac_refl

theorem fib_dvd_mul (m n : ℕ) : fib m ∣ fib (m * n) :=
nat.cases_on m (by rw [zero_mul]; refl) $ λ m,
nat.rec_on n (dvd_zero _) $ λ n ih,
show fib (nat.succ m) ∣ fib (nat.succ m * n + m + 1),
by rw [fib_add]; apply dvd_add;
[apply dvd_mul_of_dvd_left ih, apply dvd_mul_left]

theorem fib_gcd_add (m n : ℕ) : nat.gcd (fib (m+n)) (fib m) = nat.gcd (fib m) (fib n) :=
nat.cases_on n (by rw [add_zero, fib, nat.gcd_self, nat.gcd_zero_right]) $ λ n,
by rw [nat.add_succ, nat.succ_eq_add_one, fib_add, nat.gcd_comm, nat.gcd_rec];
rw [add_comm, nat.add_mul_mod_self_left, ← nat.gcd_rec];
rw [nat.gcd_comm, nat.coprime.gcd_mul_left_cancel _ (fib_succ_coprime m), nat.gcd_comm]

theorem fib_gcd_mod (m n : ℕ) : nat.gcd (fib m) (fib n) = nat.gcd (fib (m%n)) (fib n) :=
nat.mod_rec n m $ λ m, show nat.gcd (fib m) (fib n) = nat.gcd (fib (m + n)) (fib n),
from nat.cases_on n rfl $ λ n,
by rw [nat.add_succ, nat.succ_eq_add_one, fib_add]; symmetry;
rw [nat.gcd_comm, nat.gcd_rec, nat.add_mul_mod_self_right, ← nat.gcd_rec];
rw [nat.gcd_comm, nat.coprime.gcd_mul_right_cancel]; symmetry; apply fib_succ_coprime

theorem fib_gcd (m : ℕ) : ∀ n, nat.gcd (fib m) (fib n) = fib (nat.gcd m n) :=
nat.strong_induction_on m $ λ m, nat.cases_on m (λ _ _, by rw [fib, nat.gcd_zero_left, nat.gcd_zero_left]) $ λ m ih n,
have H : n % nat.succ m < nat.succ m,
  from nat.mod_lt _ $ nat.zero_lt_succ m,
by rw [nat.gcd_succ, ← ih _ H, ← fib_gcd_mod, nat.gcd_comm]