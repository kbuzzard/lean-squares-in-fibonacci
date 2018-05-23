import definitions 

local attribute [elab_as_eliminator] nat.strong_induction_on

lemma luc_fib (m : ℕ) : luc (m + 3) = 2 * fib (m + 3) + fib m :=
nat.rec_on_two m rfl rfl $ λ n ih1 ih2,
show (luc (n + 3) + luc (nat.succ n + 3)) = 2 * (fib (n + 3) + fib (n + 4)) + (fib n + fib (n + 1)),
by rw [ih1, ih2, mul_add]; simp

open nat

lemma nat.gcd_add (a b : ℕ) : gcd (a + b) b = gcd a b :=
by rw [gcd_comm, gcd_rec, add_mod_right, ← gcd_rec, gcd_comm]

lemma gcd_fib_succ (m : ℕ) : nat.gcd (fib (m + 1)) (fib m) = 1 :=
nat.rec_on m dec_trivial $ λ n ih,
show gcd (fib n + fib (n+1)) (fib (n+1)) = 1,
by rw [nat.gcd_add, gcd_comm, ih]

-- TODO -- gcd fib and luc is 1 or 2
