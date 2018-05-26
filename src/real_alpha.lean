import analysis.real tactic.norm_num tactic.ring

namespace real 
noncomputable theory 

def α := (real.sqrt 5 + 1) / 2
def β := 1 - α 

theorem root_5_squared : (sqrt 5) ^ 2 = 5 := by simp [sqr_sqrt,(by norm_num : (0:ℝ) <= 5)]

lemma αβsum : α + β = 1 := begin
  unfold β,
  unfold α,
  norm_num, -- ;-)
end 

lemma αβprod : α * β = -1 := begin
  unfold β,
  unfold α,
  rw [mul_sub,mul_one,add_div,mul_add,add_mul,add_mul], -- meh 
  simp [root_5_squared],
  sorry
--  norm_num, -- 
end

-- √ is \surd

#check sqrt_prop -- ∀ (x : ℝ), 0 ≤ sqrt x ∧ sqrt x * sqrt x = max 0 x


end real
