import mathlib_someday
import algebra.group_power

def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib n + fib (n + 1)

def Fib : ℤ → ℤ
| (int.of_nat n) := fib n
| -[1+n] := (-1)^n * fib (n+1)

lemma fib_down (n : ℕ) : Fib ↑n = ↑(fib n) := rfl

lemma Fib.is_fib : ∀ n, Fib (n+2) = Fib n + Fib (n+1) :=
begin
intro n, cases n, refl,
unfold Fib,
cases n, refl,
show Fib (-[1+ nat.succ n] + 2) = (-1) ^ nat.succ n * ↑(fib (n + 2)) + Fib (-[1+n]),
unfold Fib,
cases n, refl,
show Fib (-[1+n+2] + 2) = (-1) ^ (n+2) * ↑(fib (n + 3)) + (-1) ^ (n+1) * ↑(fib (n + 2)),
show Fib (-[1+n]) = (-1) ^ (n+2) * ↑(fib (n + 3)) + (-1) ^ (n+1) * ↑(fib (n + 2)),
unfold Fib,
simp [pow_add],
show (-1 : ℤ) ^ n * ↑(fib (n + 1)) = -((-1) ^ n * ↑(fib (n + 2))) + (-1) ^ n * (-1) ^ 2 * ↑(fib (n + 3)),
rw [(rfl : (-1 : ℤ) ^ (2 : ℕ) = 1)],
show (-1 : ℤ) ^ n * ↑(fib (n + 1)) = -((-1) ^ n * ↑(fib (n + 2))) + (-1) ^ n * 1 * ↑(fib (n + 3)),
simp,
show (-1 : ℤ) ^ n * ↑(fib (n + 1)) = (-1) ^ n * ↑(fib (n + 3)) - (-1) ^ n * ↑(fib (n + 2)),
rw [← mul_sub_left_distrib ((-1 : ℤ) ^ n) _],
suffices : ↑(fib (n + 1)) = ↑(fib (n + 3)) - ↑(fib (n + 2)), rw this,
apply eq_add_of_add_neg_eq, simp,
apply int.coe_nat_add,
end


def luc : ℕ → ℕ
| 0 := 2
| 1 := 1
| (n + 2) := luc n + luc (n + 1)

@[elab_as_eliminator]
protected def nat.rec_on_two {C : ℕ → Sort*} (n : ℕ)
  (H0 : C 0) (H1 : C 1)
  (ih : Π (n : ℕ), C n → C (nat.succ n) → C (nat.succ (nat.succ n))) :
  C n :=
nat.strong_induction_on n $ λ n, nat.cases_on n (λ _, H0) $
λ n, nat.cases_on n (λ _, H1) $ λ n ih2, ih n (ih2 n $ nat.lt_succ_of_lt $ nat.le_refl _) $
ih2 (n+1) $ nat.le_refl _

theorem int.mod_add (a b m: ℤ) : (a % m + b % m) % m = (a + b) % m :=
begin
rw [int.mod_add_mod,add_comm,int.mod_add_mod,add_comm]
end

theorem nat.mod_add_mod : ∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n :=
begin
intros m n k,
apply int.of_nat_inj,
exact int.mod_add_mod ↑m ↑n ↑k,
end 

theorem nat.mod_add (a b m : ℕ) : (a % m + b % m) % m = (a + b) % m :=
begin
apply int.of_nat_inj,
exact int.mod_add ↑a ↑b ↑m,
end 
