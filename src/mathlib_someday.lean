import data.nat.gcd

open nat 

lemma nat.gcd_add_mul (a b n : ℕ) : gcd (a + b * n) b = gcd a b := 
calc gcd (a + b * n) b = gcd b (a + b * n) : gcd_comm _ _
...                    = gcd ((a + b * n) % b) b : gcd_rec _ _
...                    = gcd (a % b) b : by simp 
...                    = gcd b a : (gcd_rec _ _).symm
...                    = gcd a b : gcd_comm _ _

lemma nat.gcd_add (a b : ℕ) : gcd (a + b) b = gcd a b := by rw [←(nat.gcd_add_mul a b 1),mul_one]

lemma nat.mod_rec (m n : ℕ) {C : ℕ → Sort*}
  (H : ∀ n, C n = C (n+m)) :
  C n = C (n%m) :=
have H1 : ∀ q r, C (r + m * q) = C r,
  from λ q, nat.rec_on q (λ r, by rw [mul_zero]; refl) $ λ n ih r,
    by rw [mul_succ, ← add_assoc, ← H, ih],
by conv in (C n) { rw [← mod_add_div n m, H1] }