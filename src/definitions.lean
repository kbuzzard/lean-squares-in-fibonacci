import mathlib_someday
import Zalpha

local notation `α` := Zalpha.units.α
local notation `β` := Zalpha.units.β

def Fib (n : ℤ) : ℤ := (↑(α^n) : ℤα).r
@[simp] lemma Fib_zero : Fib 0 = 0 := rfl
@[simp] lemma Fib_one : Fib 1 = 1 := rfl
@[simp] lemma Fib_add_two (n : ℤ) : Fib (n+2) = Fib n + Fib (n+1) :=
calc  (↑(α^(n+2)) : ℤα).r
    = (↑(α^n)*(1+α) : ℤα).r : by rw [gpow_add, units.mul_coe]; refl
... = (↑(α^n) : ℤα).r + (↑(α^(n+1)) : ℤα).r :
  by rw [gpow_add, units.mul_coe, mul_add, mul_one]; refl
@[simp] lemma Fib_add_one_add_one (n : ℤ) : Fib (n+1+1) = Fib n + Fib (n+1) :=
by rw [← Fib_add_two, add_assoc]; refl

def Luc (n : ℤ) : ℤ := (↑(α^n) + ↑(β^n) : ℤα).i
@[simp] lemma Luc_zero : Luc 0 = 2 := rfl
@[simp] lemma Luc_one : Luc 1 = 1 := rfl
@[simp] lemma Luc_add_two (n : ℤ) : Luc (n+2) = Luc n + Luc (n+1) :=
calc  (↑(α^(n+2)) + ↑(β^(n+2)) : ℤα).i
    = (↑(α^n)*(1+α) + ↑(β^n)*(1+β) : ℤα).i : by rw [gpow_add, gpow_add, units.mul_coe, units.mul_coe]; refl
... = (↑(α^n) + ↑(β^n) : ℤα).i + (↑(α^(n+1)) + ↑(β^(n+1)) : ℤα).i :
  by rw [gpow_add, units.mul_coe, mul_add, mul_one];
     rw [gpow_add, units.mul_coe, mul_add, mul_one];
     rw [← Zalpha.add_i, gpow_one, gpow_one]; ac_refl

def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := fib n + fib (n+1)

def luc : ℕ → ℕ
| 0 := 2
| 1 := 1
| (n+2) := luc n + luc (n+1)

@[elab_as_eliminator]
protected def nat.rec_on_two {C : ℕ → Sort*} (n : ℕ)
  (H0 : C 0) (H1 : C 1)
  (ih : Π (n : ℕ), C n → C (nat.succ n) → C (nat.succ (nat.succ n))) :
  C n :=
nat.strong_induction_on n $ λ n, nat.cases_on n (λ _, H0) $
λ n, nat.cases_on n (λ _, H1) $ λ n ih2, ih n (ih2 n $ nat.lt_succ_of_lt $ nat.le_refl _) $
ih2 (n+1) $ nat.le_refl _

lemma fib_down (n : ℕ) : Fib ↑n = ↑(fib n) :=
nat.rec_on_two n rfl rfl $ λ n ih1 (ih2 : Fib (n+1) = _),
show Fib (n+2) = _,
by rw [Fib_add_two, ih1, ih2, fib, int.coe_nat_add]

lemma luc_down (n : ℕ) : Luc ↑n = ↑(luc n) :=
nat.rec_on_two n rfl rfl $ λ n ih1 (ih2 : Luc (n+1) = _),
show Luc (n+2) = _,
by rw [Luc_add_two, ih1, ih2, luc, int.coe_nat_add]

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
