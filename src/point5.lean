import definitions 
import fib_mod 

lemma luc_odd_of_not_3_div (n : ℕ) : luc (3 * n + 1) % 2 = 1 ∧ 
luc (3 * n + 2) % 2 = 1 :=
begin
  split,
  { rw ←luc_mod_eq,
    rw luc_mod_2,
    simp,refl,
  },
  { rw ←luc_mod_eq,
    rw luc_mod_2,
    simp,refl,
  }
end 

--Prove that v m is not a multiple of 3 if 4 divides m. 
lemma luc_coprime_to_3_of_4_div (n : ℕ) : luc (4 * n) % 3 ≠ 0 :=
begin
  rw ←luc_mod_eq,
  rw luc_mod_3,
  -- cases n even or odd
  --case on  (n % 2 = 1)
  suffices H : n % 2 = 0 ∨ n % 2 = 1,
  cases H, 
  { -- n % 2 = 0
    suffices H2 : 4 * n % 8 = 0,
      rw H2,
      exact dec_trivial,
      change n ≡ 0 [MOD 2] at H,
      show 4 * n ≡ 0 [MOD 8],
      
      sorry,
    --have H' : 
  },
  { sorry },
  sorry, -- H
end 

--n : ℕ,
--H : n % 2 = 0
--⊢ 4 * n % 8 = 0

--#check nat.mod

--Prove that v m ≡ 7 mod 8 if m ≡ 4 mod 12 or m ≡ 8 mod 12.
