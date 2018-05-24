import definitions 
import data.list 

#check luc

#eval [luc 0,luc 1,luc 2,luc 3]

definition fib_mod (m : ℕ) : ℕ → ℕ 
| 0 := 0 % m
| 1 := 1 % m
| (n + 2) := ( (fib_mod n) + (fib_mod (n + 1)) ) % m

example (m : ℕ) : 0 % m = 0 := _

theorem fib_mod_eq (m n : ℕ) : (fib_mod m) n = (fib n) % m :=
nat.rec_on_two n (rfl) (rfl) (begin
  intros d Hd Hdplus1,
  unfold fib,
  unfold fib_mod,
  rw Hd,
  rw Hdplus1,
  exact nat.mod_add _ _ _
end)

theorem fib_mod_16 (n : ℕ) : (fib_mod 16) (n + 24) = (fib_mod 16) n :=
nat.rec_on_two n (rfl) (rfl) (begin
  intros d Hd Hdplus1,
  show (fib_mod 16 (d + 24) + fib_mod 16 (nat.succ d + 24)) % 16 = 
  (fib_mod 16 d + fib_mod 16 (nat.succ d)) % 16,
  rw Hd,rw Hdplus1,
end)

theorem fib_mod_16' (n : ℕ) : (fib_mod 16) n = (fib_mod 16) (n % 24) := sorry

#exit


def luc_mod_2 := [0,1,1]
--theorem luc_mod_3 (m : ℕ) : (luc m) % 2 = list.nth_le luc_mod_2 (m % 3) (nat.mod_lt _ (dec_trivial)) := sorry 

-- this doesn't scale
theorem luc_mod_3 (m : ℕ) :
luc (3 * m) % 2 = 0 ∧ luc (3 * m + 1) % 2 = 1 ∧ luc (3 * m + 2) % 2 = 1 :=
begin
induction m with d Hd,
  { -- base case
    split,refl,split,refl,refl
  },
  { -- inductive step
    split,
    { show luc (3 * (d + 1)) % 2 = 0,
      rw [mul_add,mul_one],
      show (luc (3 * d + 1) + luc (3 * d + 2)) % 2 = 0,

    }
  }
end 

