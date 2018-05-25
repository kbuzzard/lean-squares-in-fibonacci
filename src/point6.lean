import definitions

-- 2F(m+n) = F(m) L(n) + L(m) F(n)
lemma two_mul_fib_add (m n : ℕ) : 2 * fib (m + n) = fib m * luc n + luc m * fib n :=
nat.rec_on_two n (by rw [mul_comm]; refl)
  (nat.rec_on_two m rfl rfl $ λ n ih1 ih2,
    show 2 * (fib (n+1) + fib (nat.succ n+1))
      = (fib n + fib (nat.succ n)) * luc 1
        + (luc n + luc (nat.succ n)) * fib 1,
    by rw [mul_add, ih1, ih2, add_mul, add_mul];
      rw [add_assoc, add_left_comm (luc n * fib 1), add_assoc])
 (λ n ih1 ih2,
    show 2 * (fib (m + n) + fib (m + nat.succ n))
      = fib m * (luc n + luc (nat.succ n))
        + luc m * (fib n + fib (nat.succ n)),
    by rw [mul_add, ih1, ih2, mul_add, mul_add];
      rw [add_assoc, add_left_comm (luc m * fib n), add_assoc])

-- L(m+1)^2 + 5(-1)^m = L(m) L(m+2)
lemma luc_mul_self (m : ℕ) : luc (m+1) * luc (m+1) + 5*((m+1)%2) = luc m * luc (m+2) + 5*(m%2) :=
nat.rec_on m rfl $ λ n,
assume ih : luc (n+1) * luc (n+1) + 5*((n+1)%2) = luc n * luc (n+2) + 5*(n%2),
calc  (luc n + luc (n+1)) * luc (n+2) + 5*((n+2)%2)
    = luc n * luc (n+2) + 5*(n%2) + luc (n+1) * luc (n+2) : by rw [nat.add_mod_right, add_mul, add_right_comm]
... = luc (n+1) * (luc (n+1) + luc (n+2)) + 5*((n+1)%2) : by rw [← ih, mul_add, add_right_comm]

-- L(2m)   + 2(-1)^m = L(m)^2 and
-- L(2m+1) +  (-1)^m = L(m) L(m+1)
lemma luc_mul_base (m : ℕ) :
  luc (2*m) + 2*((m+1)%2) = luc m * luc m + 2*(m%2) ∧
  luc (2*m+1) + 1*((m+1)%2) = luc m * luc (m+1) + 1*(m%2) :=
nat.rec_on m ⟨rfl, rfl⟩ $ λ n ih, and.intro
  (suffices luc (2*n) + luc (2*n+1) + 2*((n+2)%2) + 3*((n+1)%2) = luc (n+1) * luc (n+1) + 2*((n+1)%2) + 3*((n+1)%2),
      from nat.add_right_cancel this,
    calc  luc (2*n) + luc (2*n+1) + 2*((n+2)%2) + 3*((n+1)%2)
        = luc (2*n) + luc (2*n+1) + (2+1)*((n+1)%2) + 2*((n+2)%2) : add_right_comm _ _ _
    ... = luc (2*n) + luc (2*n+1) + 2*((n+1)%2) + 1*((n+1)%2) + 2*(n%2) : by rw [add_mul, ← add_assoc, nat.add_mod_right]
    ... = luc n * luc n + luc n * luc (n+1) + 2*(n%2) + 1*(n%2) + 2*(n%2) : by rw [add_right_comm (luc (2*n)), ih.1, add_assoc (luc n * luc n + 2*(n%2)), ih.2]; ac_refl
    ... = luc n * luc n + luc n * luc (n+1) + 5*(n%2) : by rw [add_assoc, add_assoc, ← add_mul, ← add_mul]
    ... = luc n * luc (n+2) + 5*(n%2) : by rw ← mul_add; refl
    ... = luc (n+1) * luc (n+1) + 2*((n+1)%2) + 3*((n+1)%2) : by rw [add_assoc, ← add_mul, ← luc_mul_self])
  (suffices luc (2*n+1) + (luc (2*n) + luc (2*n+1)) + 1*((n+2)%2) + 4*((n+1)%2) = luc (n+1) * (luc n + luc (n+1)) + 1*((n+1)%2) + 4*((n+1)%2),
      from nat.add_right_cancel this,
    calc  luc (2*n+1) + (luc (2*n) + luc (2*n+1)) + 1*((n+2)%2) + 4*((n+1)%2)
        = luc (2*n+1) + (luc (2*n) + luc (2*n+1)) + 1*((n+2)%2) + (1*((n+1)%2) + 2*((n+1)%2) + 1*((n+1)%2)) : by rw [← add_mul, ← add_mul]
    ... = (luc (2*n+1) + 1*((n+1)%2)) + (luc (2*n) + 2*((n+1)%2)) + (luc (2*n+1) + 1*((n+1)%2)) + 1*((n+2)%2) : by ac_refl
    ... = luc (n+1) * luc n + (luc n * (luc n + luc (n+1)) + (1*(n%2) + 2*(n%2) + 1*(n%2) + 1*(n%2))) : by rw [ih.1, ih.2, nat.add_mod_right, mul_add]; ac_refl
    ... = luc (n+1) * luc n + (luc n * luc (n+2) + 5*(n%2)) : by rw [← add_mul, ← add_mul, ← add_mul]; refl
    ... = luc (n+1) * luc n + (luc (n+1) * luc (n+1) + (1+4)*((n+1)%2)) : by rw ← luc_mul_self
    ... = luc (n+1) * (luc n + luc (n+1)) + 1*((n+1)%2) + 4*((n+1)%2) : by rw [mul_add, add_mul, add_assoc, add_assoc])

-- L(2*m+n) + L(n) (-1)^m = L(m) L(m+n)
lemma luc_mul (m n : ℕ) : luc (2*m+n) + luc n * ((m+1)%2)
  = luc m * luc (m+n) + luc n * (m%2) :=
nat.rec_on_two n (luc_mul_base m).1 (luc_mul_base m).2 $ λ n ih1 ih2,
show (luc (2*m+n) + luc (2*m+nat.succ n)) + (luc n + luc (n+1)) * ((m+1)%2) = luc m * (luc (m+n) + luc (m+nat.succ n)) + (luc n + luc (nat.succ n)) * (m%2),
by rw [add_mul, add_assoc, add_left_comm (luc (2*m+nat.succ n)), ← add_assoc, ih1, ih2, mul_add, add_mul]; ac_refl

-- L(4n) + 2 = L(2n)^2
lemma luc_four_mul (n : ℕ) : luc (4 * n) + 2 = luc (2 * n) * luc (2 * n) :=
have H : _ := luc_mul (2*n) 0,
by simp at *; rw [← H, ← mul_assoc]; refl

-- F(2n) = F(n) L(n)
lemma fib_two_mul (n : ℕ) : fib (2 * n) = fib n * luc n :=
nat.bit0_inj $ by rw [bit0, ← two_mul, two_mul n, two_mul_fib_add, mul_comm]; refl

-- L(2n) ∣ 2(F(m+4n) + F(m))
lemma luc_two_mul_dvd (m n : ℕ) : luc (2 * n) ∣ 2 * (fib (m + 4 * n) + fib m) :=
⟨luc (2 * n) * fib m + luc m * fib (2 * n),
by rw [mul_add, mul_add, two_mul_fib_add, mul_comm (fib m), add_right_comm, ← add_mul, luc_four_mul];
conv in (4 * n) { change ((2 * 2) * n) };
rw [mul_assoc 2, fib_two_mul]; ac_refl⟩

-- TODO: if ¬(3 ∣ n) then fib (m + 4*n) ≡ −fib m [MOD (luc (2*n))]