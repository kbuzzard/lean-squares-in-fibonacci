import definitions 
import data.nat.gcd 
import mathlib_someday 

lemma point_4_aux (m : ℕ) : 
(luc (m + 3) = 2 * fib (m + 3) + fib m) ∧ (luc (m + 4) = 2 * fib (m + 4) + fib (m + 1)) :=

begin
  induction m with d Hd,
  { -- base case
    split;refl
  },
  { split,
      exact Hd.right,
    show (luc (d + 3) + luc (d + 4)) = 2 * (fib (d + 3) + fib (d + 4)) + (fib d + fib (d + 1)),
    rw [Hd.1,Hd.2],
    simp [mul_add],
  }
end

lemma point_4_part_a (m : ℕ) : luc (m + 3) = 2 * fib (m + 3) + fib m := (point_4_aux m).left 

open nat

#check gcd_rec 


 
lemma point_4_part_b (m : ℕ) : nat.gcd (fib (m + 1)) (fib m) = 1 := 
begin
  induction m with d Hd,
  { -- base case 
    exact dec_trivial
  },
  { -- inductive step
    show nat.gcd (fib d + fib (d + 1)) (fib (d + 1)) = 1,    
    rwa [nat.gcd_add,gcd_comm]
  }
end 

#check nat.gcd
lemma point_4_part_c (m : ℕ) : gcd (fib m) (luc m) = 1 ∨ gcd (fib m) (luc m) = 2 :=
begin
cases m with m,right,exact dec_trivial,
cases m with m,left,exact dec_trivial,
cases m with m,left,exact dec_trivial,
show gcd (fib (m + 3)) (luc (m + 3)) = 1 ∨
    gcd (fib (m + 3)) (luc (m + 3)) = 2,
rw point_4_part_a,
rw [gcd_rec,
show gcd ((fib m) % fib (m + 3)) (fib (m + 3)) = 1 ∨
    gcd ((2 * fib (m + 3) + fib m) % fib (m + 3)) (fib (m + 3)) = 2,

-- unfinished
end 

/-
import definitions
import data.nat.gcd
import data.nat.prime
-/
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

