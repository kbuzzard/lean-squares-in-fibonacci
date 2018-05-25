import analysis.real
import tactic.norm_num 
import data.nat.cast

noncomputable theory

def α := (real.sqrt 5 + 1) / 2
def β := 1 - α 

lemma αβsum : α + β = 1 := begin
  unfold β,
  unfold α,
  norm_num, -- ;-)
end 

/-
lemma αβprod : α * β = -1 := begin
  unfold β,
  unfold α,
  rw [mul_sub,mul_one,add_div,mul_add,add_mul,add_mul], -- meh 
  sorry -- :-)
end
-/

def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib n + fib (n + 1)

def Fib : ℤ → ℤ
| (int.of_nat n) := fib n
| -[1+n] := (-1)^n * fib (n+1)

def luc : ℕ → ℕ
| 0 := 2
| 1 := 1
| (n + 2) := luc n + luc (n + 1)

local attribute [elab_as_eliminator] nat.strong_induction_on

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