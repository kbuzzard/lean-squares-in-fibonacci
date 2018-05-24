import mathlib_someday
import algebra.group_power

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

@[elab_as_eliminator]
protected def nat.rec_on_two {C : ℕ → Sort*} (n : ℕ)
  (H0 : C 0) (H1 : C 1)
  (ih : Π (n : ℕ), C n → C (nat.succ n) → C (nat.succ (nat.succ n))) :
  C n :=
nat.strong_induction_on n $ λ n, nat.cases_on n (λ _, H0) $
λ n, nat.cases_on n (λ _, H1) $ λ n ih2, ih n (ih2 n $ nat.lt_succ_of_lt $ nat.le_refl _) $
ih2 (n+1) $ nat.le_refl _