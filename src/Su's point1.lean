import data.int.modeq
import data.nat.modeq
import data.nat.prime
import data.nat.gcd
import algebra.group_power
--A lot of Help from Kenny, Chris (See dirty file for more details)
open nat

theorem Ferlit (a p : ℕ) : nat.prime p → (gcd a ↑p) = 1 → a ^ (p - 1) ≡ 1 [ZMOD p] := sorry 
-- Chris has done this already! It's in the Xena library, apparently.

theorem pow_mod (a b c : ℤ) (n : ℕ) : a ≡ b [ZMOD c] → (a ^ n) ≡ (b ^ n) [ZMOD c] :=
begin
induction n, 
intro a1, 
simp,
intro a2,
have q := n_ih a2,
exact int.modeq.modeq_mul a2 q,
end

#check dvd_add 
theorem pow_neg_one (k : ℕ) (p : ℕ) : nat.prime p → p > 2 → ¬ (2 ∣ k) → (-1) ^ k ≡ - 1 [ZMOD p] := 
begin 
intros a b,
apply nat.strong_induction_on k, 
intros a1 a2 a3,
cases a1,
exact absurd a3 dec_trivial,
cases a1,
refl,
have a4 : ¬2 ∣ a1, 
intro,
apply a3,
have a5 : succ (succ a1) = a1 + 2, by simp,
rw a5,
have a6 : 2 ∣ 2 := by simp,
exact dvd_add a_1 a6,
have a5 : succ (succ a1) = a1 + 2, by simp,
rw a5, 
have : 0 < 2 , from dec_trivial,
have this1 := add_lt_add_left this a1,
have this0 : a1 + 0 = a1, by simp,
rw this0 at this1,
rw ←a5 at this1,
have Oh := a2 a1 this1 a4, 
have Ohmy := _root_.pow_add (- 1 : ℤ) a1 2,
rw Ohmy,
have End1 : (- 1 : ℤ) ^ 2 = 1 := dec_trivial, 
rw End1,
simp,
exact Oh,
end

theorem prime_thing (p : ℕ) : prime p → p > 2 → ¬ (1 ≡ -1 [ZMOD p]) := sorry 
-- Can be done immediately with Chris' lemma!

theorem prime_thing2 (x m p : ℕ) : prime p → (↑x ^ 2) ^ m ≡ ↑x ^ (2 * m) [ZMOD p] := 
begin
intro a,
have Kenni := pow_mul (↑x : ℤ) 2 m, 
rw Kenni,
end

theorem wannaprove (p : ℕ) : nat.prime p →  p ≡ 3 [ZMOD 4] →  ¬ (∃ (x : ℕ), x ^ 2 + 1 ≡ 0 [ZMOD p]) :=
begin
intros a b c,
cases c with x hx,
have e : p - 1 ≡ p - 1 [ZMOD p] := rfl, 
have d := int.modeq.modeq_add e hx,
simp at d,
have g : 1 + (p - 1 + x ^ 2) = p + x ^ 2 := by rw [← add_assoc, nat.add_sub_cancel' a.pos],
have hey1 : p + x ^ 2 = x ^ 2 + p := by simp,
have a1 : p + x ^ 2 - x ^ 2 = x ^ 2 + p - x ^ 2 := by simp, 
suffices this3 : p ∣ ((p + x ^ 2) - x ^ 2),
{
begin 
have this1 : ↑p ∣ ↑p := dvd_refl _,
have this2 := int.modeq.modeq_zero_iff.2 this1,
have this5 : x ^ 2 ≡ x ^ 2 [ZMOD p]:= by refl,
have h : p + x ^ 2 ≡ x ^ 2 [ZMOD p] := 
begin 
have this11 := int.modeq.modeq_add this5 this2,
simp at this11, 
exact this11,
end,
have f : gcd x ↑p = 1,
{
  have h1 : gcd x ↑p ∣ x, from gcd_dvd_left _ _,
  have h2 : gcd x ↑p ∣ ↑p, from gcd_dvd_right _ _,
  have h3 : gcd x ↑p ∣ x^2 + 1, 
  { 
    have hx1 := hx, 
    generalize H9 : ↑x ^ 2 + 1 = k1,
    have an1 : ↑x ^ 2 + 1 ≡ k1 [ZMOD p], 
    {
      rw ←H9, 
      simp,
    },
    have an99 : x ^ 2 + 1 ≡ 0 [MOD ↑p], 
    {
    have an9 := int.modeq.coe_nat_modeq_iff.1 hx1,
    simp at an9,
    have re1 := add_comm 1 (x ^ 2),
    have re2 := _root_.pow_two x,
    simpa using hx, 
    rw ←re2 at an9,
    simpa using an9,
    },
    from dvd_trans h2 (nat.modeq.modeq_zero_iff.1 an99),
  },
  have h4 : x ∣ x^2, 
  { have i1 := _root_.pow_two x,
    have i2 : 1 ≤ 2 := dec_trivial,
    have i3 := pow_dvd_pow x i2,
    simp at i3,
    exact i3,
  },
  have h5 : gcd x ↑p ∣ x^2, from dvd_trans h1 h4,
  have h6 : gcd x ↑p ∣ 1, from (nat.dvd_add_iff_right h5).2 h3,
  exact nat.dvd_one.1 h6,
},

have ii : p - 1 ≡ p - 1 [ZMOD p] := by refl,
have i : x ^ 2 ≡ p - 1 [ZMOD p] := 
begin
have a21 := int.modeq.modeq_add hx this2.symm,
 simp at a21,
 have a22 : ↑x ^ 2 + 1 ≡ 1 + ↑x ^ 2 [ZMOD p] := by simp,
have s1 : 1 ≡ 1 [ZMOD p] := by refl,
have s2 : (p - 1) + 1 ≡ p [ZMOD p] := by simp,
have a24 := a21.trans s2.symm, 
have a24b := a22.trans a24,
have a23 := int.modeq.modeq_add_cancel_right s1 a24b, 
exact a23,
end,
have Heyya := Ferlit x p a f, 
have important : p > 2, 
{
by_contradiction cont,
have pri := prime.ge_two a, 
have prii := le_of_not_gt cont,
have priii := le_antisymm pri prii,
have pre := int.modeq.modeq_iff_dvd.1 b,
rw ←priii at pre; exact absurd pre dec_trivial,
},
have i1 : ∃ m : ℕ, (¬ (2 ∣ m)) ∧ (p - 1 = 2 * m), 
{
    have Heynow := nat.mod_add_div p 2, 
    have H1 : ∀ n, n < 2 → n = 0 ∨ n = 1,
    from dec_trivial,
  have H2 : p % 2 = 0 ∨ p % 2 = 1,
    from H1 (p % 2) (nat.mod_lt p dec_trivial),
  cases H2 with H2 H2,
  { exfalso,
  have extra : (2 : ℤ) ∣ (4 : ℤ) := dec_trivial, 
    have wrong := int.modeq.modeq_of_dvd_of_modeq extra b, 
    unfold int.modeq at wrong, 
    have right : (3 : ℤ) % (2 : ℤ) = 1 := dec_trivial,
    rw right at wrong,
    have isthis := int.coe_nat_mod p 2,
    rw H2 at isthis, 
    change (p : ℤ) % ((2 : ℕ) : ℤ) = 1 at wrong,
    rw wrong at isthis,
    exact absurd isthis dec_trivial,
  },
existsi p/2,
split,
intro nine,
have bnew := int.modeq.coe_nat_modeq_iff.1 b,
change p ≡ 3 [MOD 4] at bnew, 
change p % 4 = 3 at bnew,
have thing11 := mod_add_div p 4,
rw bnew at thing11,
{begin
rw ← thing11 at nine,
  change 2 ∣ (3 + (2 * 2) * (p / 4)) / 2 at nine,
  rw [mul_assoc, nat.add_mul_div_left, ← nat.dvd_add_iff_left] at nine,
  { exact absurd nine dec_trivial },
  { exact dvd_mul_right _ _ },
  { exact dec_trivial },
end},
rw H2 at Heynow,
generalize H9 : 2 * (p / 2) = k, 
rw H9 at Heynow,
have F2 := nat.sub_eq_of_eq_add Heynow.symm,
exact F2, 
},
cases i1 with m b2,
cases b2 with c1 c2,
have i2 := int.modeq.modeq_iff_dvd.1 b,
cases i2, 
have j1 : x ^ (p - 1) ≡ - 1 [ZMOD p], 
{rw c2,
have s1 : 1 ≡ 1 [ZMOD p] := by refl,
have a123 := int.modeq.modeq_sub s1 hx,
simp at a123,
have a321 := int.modeq.modeq_neg a123,
simp at a321,
have a222 : (↑x ^ 2) ^ m ≡ ↑x ^ (2 * m) [ZMOD p], from (@prime_thing2 x m p a),
have a111 := pow_mod (x ^ 2) (-1) p m a321,
have g1 := pow_neg_one m p a important c1,
have afinal := a111.trans g1,
have a2222 := a222.symm,
exact a2222.trans afinal},
have Heyya1 := Heyya.symm,
have a25 := Heyya1.trans j1,
have ans := prime_thing p a important,
exact absurd a25 ans,
end},
{
rw a1,
have thes: p + x ^ 2 - x ^ 2 = p := @nat.add_sub_cancel p (x ^ 2),
have thees : x ^ 2 + p - x ^ 2 = p + x ^ 2 - x ^ 2 := by simp,
rw ←thees at thes,
rw thes,
},
end
