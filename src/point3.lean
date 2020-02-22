import definitions

open Zalpha

local notation `α` := Zalpha.units.α
local notation `β` := Zalpha.units.β

theorem α_Fib (n : ℤ) : (↑(α^n) : ℤα) = ⟨Fib (n-1), Fib n⟩ :=
int.induction_on n rfl
  (λ m ih, ext (begin 
    have ih2 : (↑(α^(m : ℤ)) : ℤα).r = Fib m,
      rw ih,
    simp only [gpow_add,
 ih,
 α_i,
 gpow_one,
 one_mul,
 units.α_coe,
 zero_mul,
 mul_i,
 add_comm,
 zero_add,
 neg_add_cancel_left,
 sub_eq_add_neg,
 α_r,
 units.coe_pow,
 units.coe_mul,
 gpow_coe_nat],
 convert ih2,
 simp,
  end) rfl)
  (λ m ih, ext (begin
    rw [sub_eq_add_neg, gpow_add, units.coe_mul, mul_i, ih],
    simp,
    apply sub_eq_of_eq_add,
    simp [-add_comm],
    convert Fib_add_two (-m - 2) using 2,
    simp, congr' 1, ring, congr' 1, ring end) rfl)

theorem β_Fib (n : ℤ) : (↑(β^n) : ℤα) = ⟨Fib (n+1), -Fib n⟩ :=
int.induction_on n rfl
  (λ m ih, ext
    ( begin rw [gpow_add, units.coe_mul, mul_i, ih, add_comm],
      convert (Fib_add_two m).symm;simp
      end
    )
    (begin simp [gpow_add] at *, simp [ih], end))
  (λ m ih, ext
    (begin simp [gpow_add] at *, simp [ih] end)
    (begin simp [gpow_add] at *, simp [ih],
      have := Fib_add_two (-m-1),
      rw [bit0, ← add_assoc, sub_add_cancel] at this,
      rw [add_comm (1 : ℤ), this], 
      simp end))

theorem Fib_αβ (m : ℤ) : ↑(Fib m) * sqrt5 = ↑(α^m) - ↑(β^m) :=
ext (by simp [α_Fib, β_Fib];
  have := Fib_add_two (m-1);
  rw [bit0, ← add_assoc, sub_add_cancel] at this;
  simp [this])
(by simp [α_Fib, β_Fib, mul_two])

theorem Luc_αβ (m : ℤ) : (↑(Luc m) : ℤα) = ↑(α^m) + ↑(β^m) :=
ext (by simp [Luc]) (by simp [α_Fib, β_Fib])