import definitions

theorem fib_add (m n : ℕ) : fib (m + n + 1) =
  fib m * fib n + fib (m + 1) * fib (n + 1) :=
nat.rec_on_two n (by unfold fib; rw [mul_zero, zero_add, mul_one]; refl)
  (by unfold fib; rw [zero_add, mul_one, mul_one]; refl) $ λ n ih1 ih2,
calc  fib (m + n + 1) + fib (m + nat.succ n + 1)
    = fib m * (fib n + fib (n+1)) + fib (m+1) * (fib (n+1) + (fib n + fib (n+1))) :
  by rw [ih1, ih2, fib, mul_add, mul_add, mul_add, mul_add, nat.succ_eq_add_one]; ac_refl

attribute [refl] dvd_refl
attribute [trans] dvd_trans

theorem fib_dvd_mul (m n : ℕ) : fib m ∣ fib (m * n) :=
nat.cases_on m (by rw [zero_mul]; refl) $ λ m,
nat.rec_on n (dvd_zero _) $ λ n ih,
show fib (nat.succ m) ∣ fib (nat.succ m * n + m + 1),
by rw [fib_add]; apply dvd_add;
[apply dvd_mul_of_dvd_left ih, apply dvd_mul_left]