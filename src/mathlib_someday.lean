import data.nat.gcd
import data.nat.modeq

attribute [elab_as_eliminator] nat.strong_induction_on
attribute [refl] dvd_refl
attribute [trans] dvd_trans
attribute [symm] nat.coprime.symm

open nat 

lemma nat.gcd_add_mul_left (a b n : ℕ) : gcd (a + b * n) b = gcd a b :=
by rw [gcd_comm, gcd_rec, add_mul_mod_self_left, ← gcd_rec, gcd_comm]

lemma nat.gcd_add_mul_right (a b n : ℕ) : gcd (a + n * b) b = gcd a b :=
by rw [gcd_comm, gcd_rec, add_mul_mod_self_right, ← gcd_rec, gcd_comm]

lemma nat.gcd_add (a b : ℕ) : gcd (a + b) b = gcd a b :=
by rw [← nat.gcd_add_mul_left a b 1, mul_one]

@[elab_as_eliminator]
lemma nat.mod_rec (m n : ℕ) {X : Sort*} {C : ℕ → X}
  (H : ∀ n, C n = C (n+m)) :
  C n = C (n%m) :=
have H1 : ∀ q r, C (r + m * q) = C r,
  from λ q, nat.rec_on q (λ r, by rw [mul_zero]; refl) $ λ n ih r,
    by rw [mul_succ, ← add_assoc, ← H, ih],
by conv in (C n) { rw [← mod_add_div n m, H1] }

@[simp] lemma nat.mod_mod (n m : ℕ) : n % m % m = n % m :=
nat.cases_on m (by simp) (λ m, mod_eq_of_lt (mod_lt _ (succ_pos _)))

def nat.mod_add (a b m : ℕ) : (a % m + b % m) % m = (a + b) % m :=
nat.modeq.modeq_add (nat.mod_mod _ _) (nat.mod_mod _ _)