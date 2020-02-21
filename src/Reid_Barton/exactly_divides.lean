import data.nat.prime
import algebra.order_functions

open nat

-- local attribute [trans] dvd_trans

-- Definition
def exactly_divides (p : ℕ) (r : ℕ) (n : ℕ) := p^r ∣ n ∧ ¬(p^(succ r) ∣ n)

notation p`^`r `∣∣`:50 n:50 := exactly_divides p r n

section
variable {p : ℕ}

-- Equivalent definitions
lemma exactly_divides' {r : ℕ} {n : ℕ} : p^r ∣∣ n ↔ (∀ i, p^i ∣ n ↔ i ≤ r) :=
begin
  apply iff.intro,
  { intros prn i, apply iff.intro,
    { intro pin,
      apply (le_or_gt _ _).resolve_right, intro i_gt_r,
      exact absurd (dvd_trans (nat.pow_dvd_pow p i_gt_r) pin) prn.right },
    { intro i_le_r,
      exact dvd.trans (pow_dvd_pow p i_le_r) (and.left prn) }
    },
  { intro h, split,
    { exact (h r).mpr (refl r) },
    { exact mt (h (succ r)).mp (not_succ_le_self r) }
  }
end

lemma exactly_divides'' {r : ℕ} {n : ℕ} (p_pos : p > 0) :
  p^r ∣∣ n ↔ ∃ k, n = p^r * k ∧ ¬(p ∣ k) :=
begin
  apply iff.intro,
  { intro prn,
    existsi n / (p^r), split,
    { exact (nat.mul_div_cancel' prn.left).symm },
    { intro d,
      have :=
      calc p^(succ r) = p^r * p            : rfl
           ...        ∣ p^r * (n / (p^r))  : mul_dvd_mul_left (p^r) d
           ...        = n                  : nat.mul_div_cancel' prn.left,
      have := prn.right, contradiction
    }
  },
  { intro h, rcases h with ⟨k, h1, h2⟩, split,
    { exact ⟨k,h1⟩ },
    { intro d,
      rw h1 at d,
      have : p ∣ k := dvd_of_mul_dvd_mul_left (pos_pow_of_pos r p_pos) d,
      contradiction
    }
  }
end

-- Uniqueness
lemma exactly_divides_unique {r s : ℕ} {n : ℕ} : p^r ∣∣ n → p^s ∣∣ n → r = s :=
λ prn psn,
have ri : ∀ i, p^i ∣ n ↔ i ≤ r := exactly_divides'.mp prn,
have si : ∀ i, p^i ∣ n ↔ i ≤ s := exactly_divides'.mp psn,
have this : ∀ i, i ≤ r ↔ i ≤ s := λ i, (ri i).symm.trans (si i),
le_antisymm ((this r).mp (le_refl r)) ((this s).mpr (le_refl s))

-- Recursion relations
lemma exactly_divides_zero {n : ℕ} (p_pos : p > 0) : ¬(p ∣ n) ↔ p^0 ∣∣ n :=
begin
  rw exactly_divides'' p_pos,
  apply iff.intro,
  { intro h, exact ⟨n, by simp, h⟩ },
  { intro h, rcases h with ⟨k, e, nd⟩, simp [e, nd] }
end

lemma exactly_divides_succ {r n : ℕ} (p_pos : p > 0) : p^r ∣∣ n ↔ p^(succ r) ∣∣ (p * n) :=
begin
  rw [exactly_divides'' p_pos, exactly_divides'' p_pos],
  apply iff.intro,
  {
    intro prn,
    rcases prn with ⟨k, h1, h2⟩,
    have h1' : p * n = p^(succ r) * k :=
    calc p * n = p * (p^r * k)  : by rw h1
         ...   = (p^r * p) * k  : by ac_refl,
    exact ⟨k, h1', h2⟩,
  },
  {
    intro psrpn,
    rcases psrpn with ⟨k, h1, h2⟩,
    have h1' : p * n = p * (p^r * k) :=
    calc p * n = p^(succ r) * k  : h1
         ...   = p * (p^r * k)   : by unfold pow nat.pow; ac_refl,
    exact ⟨k, eq_of_mul_eq_mul_left p_pos h1', h2⟩
  }
end


-- Multiplicative
lemma exactly_divides_one (hp : prime p) : p^0 ∣∣ 1 :=
(exactly_divides_zero (lt.trans dec_trivial hp.one_lt)).mp (prime.not_dvd_one hp)

lemma exactly_divides_mul {r s a b : ℕ} (hp : prime p) : p^r ∣∣ a → p^s ∣∣ b → p^(r+s) ∣∣ a*b :=
begin
  intros pra psb,
  rw exactly_divides'' (lt.trans dec_trivial hp.one_lt) at ⊢ pra psb,
  rcases pra with ⟨ka, ha1, ha2⟩,
  rcases psb with ⟨kb, hb1, hb2⟩,
  existsi ka * kb, split,
  { exact calc a * b = (p^r * ka) * (p^s * kb)  : by rw [ha1, hb1]
               ...   = (p^r * p^s) * (ka * kb)  : by ac_refl
               ...   = p^(r+s) * (ka * kb)      : by rw nat.pow_add },
  { exact prime.not_dvd_mul hp ha2 hb2 }
end

lemma exactly_divides_pow {r k a : ℕ} (hp : prime p) : p^r ∣∣ a → p^(k * r) ∣∣ a^k :=
mul_comm r k ▸
  λ pra, nat.rec_on k
           (exactly_divides_one hp)
           (λ k' ih, (exactly_divides_mul hp ih pra))

-- Gcd
lemma dvd_gcd_iff {a b k : ℕ} : k ∣ gcd a b ↔ k ∣ a ∧ k ∣ b :=
iff.intro (λ d, ⟨dvd_trans d (gcd_dvd a b).left,
                 dvd_trans d (gcd_dvd a b).right⟩)
          (λ p, and.elim p dvd_gcd)

lemma exactly_divides_gcd {r s a b : ℕ} : p^r ∣∣ a → p^s ∣∣ b → p^(min r s) ∣∣ gcd a b :=
begin
  intros pra psb,
  rw exactly_divides' at ⊢ pra psb,
  intro i,
  exact calc p^i ∣ gcd a b ↔ p^i ∣ a ∧ p^i ∣ b  : nat.dvd_gcd_iff
             ...           ↔ i ≤ r ∧ i ≤ s      : and_congr (pra i) (psb i)
             ...           ↔ i ≤ min r s        : le_min_iff.symm
end

end
