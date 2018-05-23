import analysis.real
import tactic.norm_num 

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

def luc : ℕ → ℕ
| 0 := 2
| 1 := 1
| (n + 2) := luc n + luc (n + 1)
