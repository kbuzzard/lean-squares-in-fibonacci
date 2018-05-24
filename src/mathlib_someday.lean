import data.nat.gcd

open nat 

lemma nat.gcd_add_mul (a b n : ℕ) : gcd (a + b * n) b = gcd a b := 
calc gcd (a + b * n) b = gcd b (a + b * n) : gcd_comm _ _
...                    = gcd ((a + b * n) % b) b : gcd_rec _ _
...                    = gcd (a % b) b : by simp 
...                    = gcd b a : (gcd_rec _ _).symm
...                    = gcd a b : gcd_comm _ _

lemma nat.gcd_add (a b : ℕ) : gcd (a + b) b = gcd a b := by rw [←(nat.gcd_add_mul a b 1),mul_one]
