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

