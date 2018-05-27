import analysis.real data.real.irrational Zalpha linear_algebra.basic
import data.real.basic data.nat.prime
import tactic.norm_num tactic.ring

noncomputable theory 

open nat.prime

local attribute [instance] nat.decidable_prime_1
theorem prime_five : nat.prime 5 := dec_trivial

def αℝ := (real.sqrt 5 + 1) / 2

lemma αℝ_ne_zero : αℝ ≠ 0 :=
  begin
  unfold αℝ,
  apply ne.symm, simp,
  rw [eq_div_iff_mul_eq (0 : ℝ) _ two_ne_zero],
  apply ne.symm, simp,
  rw [← eq_sub_iff_add_eq],
  simp, rw [eq_neg_iff_eq_neg],
  intro h,
  suffices : (-1 < (0 : ℝ)),
    from ne_of_lt (lt_of_lt_of_le this (real.sqrt_nonneg 5)) (eq.symm h),
  apply lt_of_add_lt_add_right _, exact 1,
  simp, exact zero_lt_one,
  end

def to_real : ℤα → ℝ := λ z, z.1 + z.2 * αℝ

def irrat_ext_add {x : ℝ} (q : ℚ) : irrational x → irrational (x + q) :=
  begin
  intro h, intro nq, apply exists.elim nq, intro q', simp, intro hadd,
  have : x = q' - q, from eq_sub_of_add_eq hadd,
  rw this at h, simp at h,
  rw [← real.of_rat_eq_cast q'] at h,
  rw [← real.of_rat_eq_cast q] at h,
  rw [← real.of_rat_neg q, ← real.of_rat_add q'] at h,
  apply h, apply exists.intro (q' + -q), simp,
  end

def irrat_ext_mul {x : ℝ} (q : ℚ) : q ≠ 0 → irrational x → irrational (x / q) :=
  begin
  intro qne0, intro h, intro nq, apply exists.elim nq, intro q', simp, intro hmul,
  have qne0' : (↑ q : ℝ) ≠ 0, { simp, exact qne0, },
  have : x = q' * q, from eq.symm ((eq_div_iff_mul_eq _ _ qne0').1 (eq.symm hmul)),
  rw this at h,
  rw [← real.of_rat_eq_cast q'] at h,
  rw [← real.of_rat_eq_cast q] at h,
  rw [← real.of_rat_mul q'] at h,
  apply h, apply exists.intro (q' * q), simp,
  end

def irrat_ext_neg {x : ℝ} : irrational x → irrational (-x) :=
  begin
  intro h,
  have neg1ne0 := neg_ne_zero.2 (@one_ne_zero ℚ _),
  have := irrat_ext_mul (-1) neg1ne0 h,
  simp at this, rw [div_neg x (one_ne_zero), div_one] at this,
  exact this,
  end

def irrat_ext_inv {x : ℝ} : x ≠ 0 → irrational x → irrational (x⁻¹) :=
  begin
  intro xne0, intro h, intro nq, apply exists.elim nq, intro q, simp, intro hinv,
  rw [← division_ring.inv_inv xne0] at h,
  apply h, apply exists.intro (q⁻¹), rw hinv,
  exact eq.symm (rat.cast_inv q),
  end

section
open real rat
theorem sqrt_five_irrational : irrational (sqrt 5)
| ⟨⟨n, d, h, c⟩, e⟩ := begin
  simp [num_denom', mk_eq_div] at e,
  have := @mul_self_sqrt 5 (le_of_lt (add_pos four_pos zero_lt_one)),
  have d0 : (0:ℝ) < d := nat.cast_pos.2 h,
  rw [e, div_mul_div, div_eq_iff_mul_eq (ne_of_gt $ mul_pos d0 d0),
      ← int.cast_mul, ← int.nat_abs_mul_self] at this,
  revert c this, generalize : n.nat_abs = a, intros,
  have E : 5 * (d * d) = a * a := (@nat.cast_inj ℝ _ _ _ _ _).1 (by simpa),
  have ae : 5 ∣ a,
  { refine (or_self _).1 (prime_five.dvd_mul.1 _),
    rw ← E, apply dvd_mul_right },
  have de : 5 ∣ d,
  { have := mul_dvd_mul ae ae,
    refine (or_self _).1 (prime_five.dvd_mul.1 _),
    rwa [← E, nat.mul_dvd_mul_iff_left (nat.succ_pos 4)] at this },
  refine nat.not_coprime_of_dvd_of_dvd _ ae de c, from dec_trivial,
end
end

def one_half : ℚ := (1 : ℚ) / (2 : ℚ)

theorem αℝ_irrational : irrational αℝ :=
  begin
  have irrat := irrat_ext_add (one_half) (irrat_ext_mul 2 two_ne_zero sqrt_five_irrational),
  have alphar : real.sqrt 5 / ↑(2 : ℚ) + ↑(one_half) = αℝ,
    unfold one_half, unfold αℝ,
    rw [eq_div_iff_mul_eq _ _ two_ne_zero],
    rw [right_distrib],
    have : (one_half : ℝ) * 2 = (1 : ℝ),
      show (one_half : ℝ) * 2 = (1 : ℝ),
      symmetry, transitivity, symmetry, exact rat.cast_one,
      have : (2 : ℝ) = (2 : ℚ),
        show (1 + 1 : ℝ) = (1 + 1 : ℚ),
        rw [rat.cast_add, rat.cast_one],
      rw this,
      rw [← rat.cast_mul, rat.cast_inj], refl,
    unfold_coes, unfold_coes at this, unfold one_half at this,
    rw this,
    have : (rat.cast 2 : ℝ) = 2,
      show (rat.cast (1 + 1) : ℝ) = 1 + 1,
      show (↑ (1 + 1 : ℚ) : ℝ) = 1 + 1,
      rw [rat.cast_add, rat.cast_one],
    rw this, simp, exact div_mul_cancel (real.sqrt 5) two_ne_zero,
  rw alphar at irrat, exact irrat,
  end

lemma αℝ.linear_independent : ∀ z : ℤα, to_real z = 0 → z = 0 :=
  begin
  intro z, intro h, unfold to_real at h,
  rw [← eq_sub_iff_add_eq] at h, simp at h, rw [eq_neg_iff_eq_neg] at h,
  suffices : z.i = 0,
  {
    rw this at h,
    simp at h,
    rw [← eq_div_iff_mul_eq _ 0 αℝ_ne_zero] at h,
    simp at h,
    exact Zalpha.ext this h,
  },
  by_contradiction zine0,
  have zine0' : (↑ z.i : ℝ) ≠ 0, { simp, exact zine0, },
  rw [iff.intro eq.symm eq.symm] at h,
  rw [neg_eq_neg_one_mul, ← eq_div_iff_mul_eq _ _ zine0'] at h,
  rw [mul_div_assoc, mul_div_comm] at h,
  rw [mul_comm, iff.intro eq.symm eq.symm, ← eq_div_iff_mul_eq _ (-1) αℝ_ne_zero] at h,
  have : ∀ (i : ℤ), (i : ℝ) = ↑ (↑ (i : ℤ) : ℚ),
  { intro i, symmetry,
    apply int.eq_cast (rat.cast ∘ int.cast),
    simp,
    show rat.cast (int.cast (1 : ℤ)) = (1 : ℝ),
    show rat.cast (↑ (1 : ℤ)) = (1 : ℝ),
    show ↑ (↑ (1 : ℤ) : ℚ) = (1 : ℝ),
    simp,
    intros, simp,
    show rat.cast (int.cast (x + y)) = rat.cast (int.cast x) + rat.cast (int.cast y),
    show rat.cast (↑ (x + y)) = rat.cast (↑ x) + rat.cast (↑ y),
    show (↑ (↑ (x + y) : ℚ) : ℝ) = ↑ (↑ x : ℚ) + ↑ (↑ y : ℚ), simp,
  },
  rw [this z.i, this z.r] at h,
  rw [← @rat.cast_div ℝ _ _ z.r z.i] at h,
  rw [division_def (-1) αℝ, mul_comm, mul_neg_one] at h,
  apply irrat_ext_neg (irrat_ext_inv αℝ_ne_zero αℝ_irrational),
  apply exists.intro, exact eq.symm h,
  end

@[simp] lemma to_real_α : to_real Zalpha.α = αℝ := by unfold to_real; simp
@[simp] lemma to_real_0 : to_real (0 : ℤα) = (0 : ℝ) := by unfold to_real; simp
@[simp] lemma to_real_1 : to_real 1 = 1 := by unfold to_real; simp

lemma αℝ.sqrd : αℝ*αℝ = αℝ + 1 :=
have h : (0 : ℝ) ≤ 5 := by norm_num,
begin
  unfold αℝ,
  rw [div_mul_div, mul_add, mul_one, add_mul, one_mul, ← pow_two, real.sqr_sqrt h],
  ring,
end

instance : is_ring_hom to_real :=
{ map_add :=
    begin
    intros, unfold to_real, simp [right_distrib],
    end
, map_mul :=
    begin
    intros, unfold to_real, simp [left_distrib, right_distrib],
    have : (↑(x.r) * αℝ * ((y.r) * αℝ)) = x.r * y.r * (αℝ * αℝ), ac_refl,
    rw [this, αℝ.sqrd],
    simp [left_distrib], ac_refl,
    end
, map_one :=
    begin
    unfold to_real, simp,
    end
}

lemma to_real.injective : function.injective to_real :=
  begin
  intros z₁ z₂ h,
  rw [← sub_eq_zero] at h,
  rw [← sub_eq_zero],
  rw [← is_ring_hom.map_sub to_real] at h,
  exact αℝ.linear_independent _ h,
  end

lemma to_real.inj : ∀ a b, to_real a = to_real b ↔ a = b :=
  begin
  intros, constructor, exact @to_real.injective a b, intro h, rw h
  end

/-instance : integral_domain Zalpha :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
  begin
  intros a b h,
  rw [← to_real.inj, to_real.is_ring_hom.map_mul] at h,
  simp at h,
  have := eq_zero_or_eq_zero_of_mul_eq_zero h,
  cases this,
  rw [← to_real_0, to_real.inj _ 0] at this,
  left, exact this,
  rw [← to_real_0, to_real.inj _ 0] at this,
  right, exact this,
  end,
  zero_ne_one := dec_trivial,
  ..Zalpha.comm_ring
}-/
