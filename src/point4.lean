import definitions 

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

lemma point_4_part_a (m : ℕ) : luc (m + 3) = 2 * fib (m + 3) + fib m := (aux m).left 

open nat

#check gcd_rec 

lemma nat.gcd_aux (a b : ℕ) : gcd (a + b) b = gcd a b := 
calc gcd (a + b) b = gcd b (a + b) : gcd_comm _ _
...                = gcd ((a + b) % b) b : gcd_rec _ _
...                = gcd (a % b) b : by simp
...                = gcd b a : (gcd_rec _ _).symm 
...                = gcd a b : gcd_comm _ _
 
lemma point_4_part_b (m : ℕ) : nat.gcd (fib (m + 1)) (fib m) = 1 := 
begin
  induction m with d Hd,
  { -- base case 
    exact dec_trivial
  },
  { -- inductive step
    show nat.gcd (fib d + fib (d + 1)) (fib (d + 1)) = 1,    
    rwa [nat.gcd_aux,gcd_comm]
  }
end 

-- TODO -- gcd fib and luc is 1 or 2
