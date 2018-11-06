import definitions

open Zalpha

local notation `α` := Zalpha.units.α
local notation `β` := Zalpha.units.β

theorem α_Fib (n : ℤ) : (↑(α^n) : ℤα) = ⟨Fib (n-1), Fib n⟩ :=
int.induction_on n rfl
  (λ n ih, ext (by simp [gpow_add, ih]) rfl)
  (λ n ih, ext (by simp [gpow_add, ih];
    apply sub_eq_of_eq_add;
    simpa [-add_comm] using Fib_add_two (n-2)) rfl)

theorem β_Fib (n : ℤ) : (↑(β^n) : ℤα) = ⟨Fib (n+1), -Fib n⟩ :=
int.induction_on n rfl
  (λ n ih, ext
    (by simp [gpow_add, ih]; rw [← Fib_add_two n]; refl)
    (by simp [gpow_add, ih]))
  (λ n ih, ext
    (by simp [gpow_add, ih])
    (by simp [gpow_add, ih];
      have := Fib_add_two (n-1);
      rw [bit0, ← add_assoc, sub_add_cancel] at this;
      simp [this]))

theorem Fib_αβ (m : ℤ) : ↑(Fib m) * sqrt5 = ↑(α^m) - ↑(β^m) :=
ext (by simp [α_Fib, β_Fib];
  have := Fib_add_two (m-1);
  rw [bit0, ← add_assoc, sub_add_cancel] at this;
  simp [this])
(by simp [α_Fib, β_Fib, mul_two])

theorem Luc_αβ (m : ℤ) : (↑(Luc m) : ℤα) = ↑(α^m) + ↑(β^m) :=
ext (by simp [Luc]) (by simp [α_Fib, β_Fib])