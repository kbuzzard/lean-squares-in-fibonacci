import definitions 
import data.list.basic

definition fib_mod (m : ℕ) : ℕ → ℕ 
| 0 := 0 % m
| 1 := 1 % m
| (n + 2) := ( (fib_mod n) + (fib_mod (n + 1)) ) % m

def luc_mod (m : ℕ) : ℕ → ℕ
| 0 := 2 % m
| 1 := 1 % m
| (n + 2) := ( (luc_mod n) + (luc_mod (n + 1)) ) % m

theorem luc_mod_is_luc (m : ℕ) : ∀ r : ℕ,
luc_mod m r = (luc r) % m  
| 0 := rfl
| 1 := rfl 
| (n + 2) := begin
have Hn := luc_mod_is_luc n,
have Hnp1 := luc_mod_is_luc (n + 1),
unfold luc_mod,
unfold luc,
rw Hn,
rw Hnp1,
show (luc n % m + luc (n + 1) % m) % m = (luc n + luc (n + 1)) % m,
apply nat.mod_add,
end 



theorem fib_mod_eq (m n : ℕ) : (fib_mod m) n = (fib n) % m :=
nat.rec_on_two n (rfl) (rfl) (begin
  intros d Hd Hdplus1,
  unfold fib,
  unfold fib_mod,
  rw Hd,
  rw Hdplus1,
  exact nat.mod_add _ _ _
end)

theorem luc_mod_eq (m n : ℕ) : (luc_mod m) n = (luc n) % m :=
nat.rec_on_two n (rfl) (rfl) (begin
  intros d Hd Hdplus1,
  unfold luc,
  unfold luc_mod,
  rw Hd,
  rw Hdplus1,
  exact nat.mod_add _ _ _
end)


theorem fib_mod_16_aux (n : ℕ) : (fib_mod 16) (n + 24) = (fib_mod 16) n :=
nat.rec_on_two n (rfl) (rfl) (begin
  intros d Hd Hdplus1,
  show (fib_mod 16 (d + 24) + fib_mod 16 (nat.succ d + 24)) % 16 = 
  (fib_mod 16 d + fib_mod 16 (nat.succ d)) % 16,
  rw Hd,rw Hdplus1,
end)

theorem fib_mod_16 (n : ℕ) : (fib_mod 16) n = (fib_mod 16) (n % 24) := 
begin
  have H : ∀ n k, fib_mod 16 (n + 24 * k) = (fib_mod 16) n,
  { intros n k, 
    induction k with d Hd,
    -- base case
    { refl},
    -- inductive step
    { show fib_mod 16 (n + 24 * (d + 1)) = fib_mod 16 n,
      rwa [mul_add,←add_assoc,mul_one,fib_mod_16_aux],
    },
  },
  conv begin
    to_lhs,
    rw ←nat.mod_add_div n 24,
  end,
  rw H (n % 24) (n / 24)
end

theorem luc_mod_8_aux (n : ℕ) : (luc_mod 8) (n + 12) = (luc_mod 8) n :=
nat.rec_on_two n (rfl) (rfl) (begin
  intros d Hd Hdplus1,
  show (luc_mod 8 (d + 12) + luc_mod 8 (nat.succ d + 12)) % 8 = 
  (luc_mod 8 d + luc_mod 8 (nat.succ d)) % 8,
  rw Hd,rw Hdplus1,
end)

theorem luc_mod_8 (n : ℕ) : (luc_mod 8) n = (luc_mod 8) (n % 12) := 
begin
  have H : ∀ n k, luc_mod 8 (n + 12 * k) = (luc_mod 8) n,
  { intros n k, 
    induction k with d Hd,
    -- base case
    { refl},
    -- inductive step
    { show luc_mod 8 (n + 12 * (d + 1)) = luc_mod 8 n,
      rwa [mul_add,←add_assoc,mul_one,luc_mod_8_aux],
    },
  },
  conv begin
    to_lhs,
    rw ←nat.mod_add_div n 12,
  end,
  rw H (n % 12) (n / 12)
end

theorem luc_mod_3_aux (n : ℕ) : (luc_mod 3) (n + 8) = (luc_mod 3) n :=
nat.rec_on_two n (rfl) (rfl) (begin
  intros d Hd Hdplus1,
  show (luc_mod 3 (d + 8) + luc_mod 3 (nat.succ d + 8)) % 3 = 
  (luc_mod 3 d + luc_mod 3 (nat.succ d)) % 3,
  rw Hd,rw Hdplus1,
end)

theorem luc_mod_3 (n : ℕ) : (luc_mod 3) n = (luc_mod 3) (n % 8) := 
begin
  have H : ∀ n k, luc_mod 3 (n + 8 * k) = (luc_mod 3) n,
  { intros n k, 
    induction k with d Hd,
    -- base case
    { refl},
    -- inductive step
    { show luc_mod 3 (n + 8 * (d + 1)) = luc_mod 3 n,
      rwa [mul_add,←add_assoc,mul_one,luc_mod_3_aux],
    },
  },
  conv begin
    to_lhs,
    rw ←nat.mod_add_div n 8,
  end,
  rw H (n % 8) (n / 8)
end

theorem luc_mod_2_aux (n : ℕ) : (luc_mod 2) (n + 3) = (luc_mod 2) n :=
nat.rec_on_two n (rfl) (rfl) (begin
  intros d Hd Hdplus1,
  show (luc_mod 2 (d + 3) + luc_mod 2 (nat.succ d + 3)) % 2 = 
  (luc_mod 2 d + luc_mod 2 (nat.succ d)) % 2,
  rw Hd,rw Hdplus1,
end)

theorem luc_mod_2 (n : ℕ) : (luc_mod 2) n = (luc_mod 2) (n % 3) := 
begin
  have H : ∀ n k, luc_mod 2 (n + 3 * k) = (luc_mod 2) n,
  { intros n k, 
    induction k with d Hd,
    -- base case
    { refl},
    -- inductive step
    { show luc_mod 2 (n + 3 * (d + 1)) = luc_mod 2 n,
      rwa [mul_add,←add_assoc,mul_one,luc_mod_2_aux],
    },
  },
  conv begin
    to_lhs,
    rw ←nat.mod_add_div n 3,
  end,
  rw H (n % 3) (n / 3)
end
