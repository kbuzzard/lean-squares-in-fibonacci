import Zalpha number_theory.pell

instance nonsquare_five : zsqrtd.nonsquare 5 :=
⟨λ n, nat.cases_on n dec_trivial $ λ n,
  nat.cases_on n dec_trivial $ λ n,
  nat.cases_on n dec_trivial $ λ n,
  ne_of_lt $ calc 5 < 3 * 3 : dec_trivial
    ... ≤ 3 * (n+3) : nat.mul_le_mul_left _ (nat.le_add_left _ _)
    ... ≤ (n+3) * (n+3) : nat.mul_le_mul_right _ (nat.le_add_left _ _)⟩

namespace Zalpha

-- multiply by two, i.e. (a+bα) ↦ 2a+b(1+√5)
def to_Zsqrt5 (z : ℤα) : ℤ√5 :=
⟨2*z.i + z.r, z.r⟩

@[simp] lemma to_Zsqrt5_zero : to_Zsqrt5 0 = 0 := rfl

@[simp] lemma to_Zsqrt5_add (z w : ℤα) :
  to_Zsqrt5 (z + w) = to_Zsqrt5 z + to_Zsqrt5 w :=
by simp [to_Zsqrt5, mul_add]

@[simp] lemma to_Zsqrt5_mul (z w : ℤα) :
  to_Zsqrt5 (z * w) * 2 = to_Zsqrt5 z * to_Zsqrt5 w :=
by rw [zsqrtd.ext, mul_two]; unfold to_Zsqrt5; split; simp; ring

theorem to_Zsqrt5_inj : function.injective to_Zsqrt5 :=
begin
  intros z w H,
  unfold to_Zsqrt5 at H,
  cases zsqrtd.ext.1 H with H1 H2,
  dsimp at H1 H2,
  rw [H2, add_right_cancel_iff] at H1,
  have H3 := eq_of_mul_eq_mul_left dec_trivial H1,
  apply ext; assumption
end

instance : decidable_linear_ordered_comm_ring ℤα :=
{ le := λ z w, to_Zsqrt5 z ≤ to_Zsqrt5 w,
  le_refl := λ z, show to_Zsqrt5 z ≤ to_Zsqrt5 z, from le_refl _,
  le_trans := λ z₁ z₂ z₃ H12 H23, show to_Zsqrt5 z₁ ≤ to_Zsqrt5 z₃, from le_trans H12 H23,
  le_antisymm := λ z w Hzw Hwz, to_Zsqrt5_inj $ le_antisymm Hzw Hwz,
  lt := λ z w, to_Zsqrt5 z < to_Zsqrt5 w,
  lt_iff_le_not_le := λ z w, show to_Zsqrt5 z < to_Zsqrt5 w ↔ _, from lt_iff_le_not_le,
  add_le_add_left := λ z₁ z₂ H12 z₃, calc _ = _ : to_Zsqrt5_add _ _
    ... ≤ _ : zsqrtd.add_le_add_left _ _ H12 _
    ... = _ : (to_Zsqrt5_add _ _).symm,
  add_lt_add_left := λ z₁ z₂ H12 z₃, calc _ = _ : to_Zsqrt5_add _ _
    ... < _ : zsqrtd.add_lt_add_left _ _ H12 _
    ... = _ : (to_Zsqrt5_add _ _).symm,
  mul_nonneg := λ z w (Hz : to_Zsqrt5 z ≥ 0) (Hw : to_Zsqrt5 w ≥ 0),
    show to_Zsqrt5 (z * w) ≥ 0,
    from nonneg_of_mul_nonneg_right
      (trans_rel_left _ (mul_nonneg Hz Hw) (to_Zsqrt5_mul z w).symm)
      (add_pos zero_lt_one zero_lt_one),
  mul_pos := λ z w (Hz : to_Zsqrt5 z > 0) (Hw : to_Zsqrt5 w > 0),
    show to_Zsqrt5 (z * w) > 0,
    from pos_of_mul_pos_right
      (trans_rel_left _ (mul_pos Hz Hw) (to_Zsqrt5_mul z w).symm)
      (add_nonneg zero_le_one zero_le_one),
  le_total := λ z w, zsqrtd.le_total _ _,
  zero_lt_one := show 0 < to_Zsqrt5 1, from dec_trivial,
  decidable_le := λ z w, show decidable (to_Zsqrt5 z ≤ to_Zsqrt5 w), by apply_instance,
  .. Zalpha.integral_domain }

end Zalpha