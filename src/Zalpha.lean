import algebra.group_power
import definitions
import data.nat.gcd
import data.nat.prime
import tactic.ring

-- Z[alpha] where alpha := (1 + sqrt(5))/2, representing the minimal ring
-- (with addition, subtraction, and multiplication) containing the roots
-- of x^2-x-1 = 0: alpha := (1 + sqrt(5))/2 and beta (1 - sqrt(5))/2
-- (with beta < alpha)
--
-- i as in int, r as in root
@[derive decidable_eq]
structure Zalpha : Type :=
(i : ℤ) (r : ℤ)

notation `ℤα` := Zalpha

namespace Zalpha

@[simp] theorem eta : ∀ z : ℤα, Zalpha.mk z.i z.r = z
| ⟨a, b⟩ := rfl

theorem ext : ∀ {z w : ℤα}, z.i = w.i → z.r = w.r → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

theorem ext_iff {z w : ℤα} : z = w ↔ z.i = w.i ∧ z.r = w.r :=
⟨λ H, by simp [H], and.rec ext⟩

def of_int (z : ℤ) : ℤα := ⟨z, 0⟩
@[simp] lemma of_int_i (r : ℤ) : (of_int r : ℤα).i = r := rfl
@[simp] lemma of_int_r (r : ℤ) : (of_int r : ℤα).r = 0 := rfl

@[reducible] def of_nat (n : ℕ) : ℤα := of_int n
@[simp] lemma of_nat_i (r : ℕ) : (of_nat r : ℤα).i = r := rfl
@[simp] lemma of_nat_r (r : ℕ) : (of_nat r : ℤα).r = 0 := rfl

instance : has_zero ℤα := ⟨⟨(0 : ℤ), 0⟩⟩
instance : inhabited ℤα := ⟨0⟩

@[simp] lemma zero_i : (0 : ℤα).i = 0 := rfl
@[simp] lemma zero_r : (0 : ℤα).r = 0 := rfl
lemma of_int_zero : (of_int (0 : ℤ) : ℤα) = 0 := rfl

instance : has_one ℤα := ⟨⟨(1 : ℤ), 0⟩⟩

@[simp] lemma one_i : (1 : ℤα).i = 1 := rfl
@[simp] lemma one_r : (1 : ℤα).r = 0 := rfl
@[simp] lemma of_int_one : (of_int (1 : ℤ) : ℤα) = 1 := rfl

def α : ℤα := ⟨0, 1⟩

@[simp] lemma α_i : α.i = 0 := rfl
@[simp] lemma α_r : α.r = 1 := rfl

def β : ℤα := ⟨1, -1⟩

@[simp] lemma β_i : β.i = 1 := rfl
@[simp] lemma β_r : β.r = -1 := rfl

instance : has_add ℤα := ⟨λ z w, ⟨z.i + w.i, z.r + w.r⟩⟩

@[simp] lemma add_i (z w : ℤα) : (z + w).i = z.i + w.i := rfl
@[simp] lemma add_r (z w : ℤα) : (z + w).r = z.r + w.r := rfl
@[simp] lemma of_int_add (r s : ℤ) : (of_int (r + s : ℤ) : ℤα) = of_int (r + s) := rfl

@[simp] lemma of_int_bit0 (r : ℤ) : (of_int (bit0 r : ℤ) : ℤα) = bit0 (of_int r) := rfl
@[simp] lemma of_int_bit1 (r : ℤ) : (of_int (bit1 r : ℤ) : ℤα) = bit1 (of_int r) := rfl

instance : has_neg ℤα := ⟨λ z, ⟨-z.i, -z.r⟩⟩

@[simp] lemma neg_i (z : ℤα) : (-z).i = -z.i := rfl
@[simp] lemma neg_r (z : ℤα) : (-z).r = -z.r := rfl
@[simp] lemma of_int_neg (r : ℤ) : (of_int (-r : ℤ) : ℤα) = -of_int r := ext_iff.2 $ by simp

--   bα * dα
-- = (b/2 + b*sqrt(5)/2) * (d/2 + d*sqrt(5)/2)
-- = (b*d/4 + b*d*5/4) + (b*d*sqrt(5)/4) + (b*d*sqrt(5)/4)
-- = 3*b*d/2 + b*d*sqrt(5)/2
-- = 2*b*d/2 + b*d*α
-- = b*d + b*d*α

--   (a + bα) * (c + dα)
-- = a*c + (a*d + b*c)α + bα * dα
-- = a*c + (a*d + b*c)α + b*d + b*d*α
-- = (a*c + b*d) + (a*d + b*c + b*d)α

-- a: z.i, b: z.r,
-- c: w.i, d: w.r
instance : has_mul ℤα := ⟨λ z w, ⟨z.i * w.i + z.r * w.r, z.i * w.r + z.r * w.i + z.r * w.r⟩⟩

@[simp] lemma mul_i (z w : ℤα) : (z * w).i = z.i * w.i + z.r * w.r := rfl
@[simp] lemma mul_r (z w : ℤα) : (z * w).r = z.i * w.r + z.r * w.i + z.r * w.r := rfl
@[simp] lemma of_int_mul (r s : ℤ) : (of_int (r * s : ℤ) : ℤα) = of_int r * of_int s := ext_iff.2 $ by simp

lemma mk_eq_add_mul_α (a b : ℤ) : Zalpha.mk a b = of_int a + of_int b * α :=
ext_iff.2 $ by simp

@[simp] lemma re_add_im (z : ℤα) : (of_int z.i : ℤα) + of_int z.r * α = z :=
ext_iff.2 $ by simp

instance : comm_ring ℤα :=
by refine
{ add      := (+),
  zero     := 0,
  neg      := has_neg.neg,
  mul      := (*),
  one      := 1,
  mul_comm := by intros; apply ext; simp [mul_comm],
  /-
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
    intros a b h, rw ext_iff at h, simp at h,
    by_contradiction h', -- rw [@ext_iff a, @ext_iff b] at h', simp at h',
    rw [not_or_distrib] at h',
    end
  -/
  ..
}; { intros; apply ext; simp [left_distrib, right_distrib, mul_assoc] }

@[simp] lemma comm_ring_zero : comm_ring.zero ℤα = 0 := rfl

@[simp] lemma of_int_eq_coe (r : ℤ) : ↑r = of_int r :=
  eq.symm (int.eq_cast of_int rfl (λ _ _, rfl) r)
@[simp] lemma coe_int_i (r : ℤ) : (r : ℤα).i = r := by simp
@[simp] lemma coe_int_r (r : ℤ) : (r : ℤα).r = 0 := by simp

@[simp] lemma of_nat_eq_coe (r : ℕ) : ↑r = of_nat r :=
  eq.symm (nat.eq_cast of_nat rfl rfl (λ a b, rfl) r)
@[simp] lemma coe_nat_i (r : ℕ) : (↑r : ℤα).i = r := by simp
@[simp] lemma coe_nat_r (r : ℕ) : (↑r : ℤα).r = 0 := by simp

@[simp] lemma of_fib_r (n : ℕ) : (↑(fib n) : ℤα).r = 0 := by simp
@[simp] lemma of_fib_i (n : ℕ) : (↑(fib n) : ℤα).i = fib n := by simp

@[simp] theorem of_int_inj {z w : ℤ} : (z : ℤα) = w ↔ z = w :=
⟨eq.substr (of_int_eq_coe z) $ eq.substr (of_int_eq_coe w) (congr_arg i), congr_arg _⟩

@[simp] theorem of_int_eq_zero {z : ℤ} : (z : ℤα) = 0 ↔ z = 0 :=
  by show (z : ℤα) = ↑0 ↔ z = ↑0; exact @of_int_inj z 0
@[simp] theorem of_int_ne_zero {z : ℤ} : (z : ℤα) ≠ 0 ↔ z ≠ 0 :=
  not_congr of_int_eq_zero

@[simp] lemma of_nat_eq_nat_cast (r : ℕ) : nat.cast r = of_nat r :=
  eq.symm (nat.eq_cast of_nat rfl rfl (λ a b, rfl) r)
@[simp] lemma nat_cast_i (r : ℕ) : (nat.cast r : ℤα).i = r := by simp
@[simp] lemma nat_cast_r (r : ℕ) : (nat.cast r : ℤα).i = r := by simp

/- Extra instances to short-circuit type class resolution -/
instance : has_sub ℤα            := by apply_instance
instance : add_comm_monoid ℤα    := by apply_instance
instance : add_monoid ℤα         := by apply_instance
instance : monoid ℤα             := by apply_instance
instance : comm_monoid ℤα        := by apply_instance
instance : comm_semigroup ℤα     := by apply_instance
instance : semigroup ℤα          := by apply_instance
instance : add_comm_semigroup ℤα := by apply_instance
instance : add_semigroup ℤα      := by apply_instance
instance : comm_semiring ℤα      := by apply_instance
instance : semiring ℤα           := by apply_instance
instance : ring ℤα               := by apply_instance
instance : distrib ℤα            := by apply_instance

instance : has_pow ℤα ℕ := { pow := @monoid.pow ℤα _ }

instance : has_repr ℤα :=
{ repr := λ a, repr a.i ++ " + " ++ repr a.r ++ "α" }

@[simp]
lemma coe_int_add {a b : ℤ} : (of_int (a + b) : ℤα) = of_int a + of_int b := rfl
@[simp]
lemma coe_int_neg {a : ℤ} : -of_int a = of_int (-a) := rfl
@[simp]
lemma coe_nat_add {a b : ℕ} : (of_int (↑(a + b) : ℤ) : ℤα) = of_int ↑a + of_int ↑b :=
by rw [int.coe_nat_add, @coe_int_add ↑a ↑b]

@[simp] lemma αβsum : α + β = 1 := rfl
@[simp] lemma αβprod : α * β = -1 := rfl
lemma α_sqr : α^2 = α + 1 := rfl

theorem α_mul_right (z : ℤα) : α * z = ⟨z.r, z.i + z.r⟩ :=
by apply ext; simp

theorem α_fib (n : ℕ) : α^(n+1) = ⟨Fib n, Fib (n+1)⟩ :=
begin
  induction n with n ih, { refl },
  change α*α^(n + 1) = ⟨Fib (n+1), Fib (n+2)⟩,
  rw ih, apply ext; simp [-add_comm, Fib.is_fib]
end

theorem β_mul_right (z : ℤα) : β * z = ⟨z.i - z.r, -z.i⟩ :=
by apply ext; simp

-- #eval Fib (-1)
-- #eval β * β
-- #eval β * β * β * β * β

theorem β_fib (n : ℕ) : β^n = ⟨Fib (n+1), -Fib (n)⟩ :=
begin
  induction n with n ih, { refl },
  change β*β^n = ⟨Fib (n+2), -Fib (n+1)⟩,
  rw ih, apply ext; simp [-add_comm, Fib.is_fib]; simp
end

def sqrt5 : ℤα := ⟨-1, 2⟩
@[simp] lemma sqrt5_i : sqrt5.i = -1 := rfl
@[simp] lemma sqrt5_r : sqrt5.r = 2 := rfl
@[simp] lemma sqrt5_squared : sqrt5 ^ 2 = 5 := rfl

/- conj (a + bα)
 = a + bβ
 = a + b(1 - α)
 = (a + b) - bα
-/
def conj (z : ℤα) : ℤα := ⟨z.i + z.r, -z.r⟩

/- norm (a + bα)
 = (a + bα) (a + bβ)
 = a² + ab(α + β) + b²αβ
 = a² + ab - b²
-/
def norm (z : ℤα) : ℤ := z.i * z.i + z.i * z.r - z.r * z.r

@[simp] lemma add_conj (z : ℤα) : z + conj z = 2 * z.i + z.r :=
by apply ext; simp [conj, two_mul]

@[simp] lemma mul_conj (z : ℤα) : z * conj z = norm z :=
by apply ext; simp [conj, norm, mul_add, mul_comm]

lemma norm_mul (z w : ℤα) : norm (z * w) = norm z * norm w :=
by simp [norm, add_mul, mul_add]; ring

local attribute [instance] nat.decidable_prime_1
theorem prime_five : nat.prime 5 := dec_trivial

lemma zero_of_norm_zero (z : ℤα) (H : norm z = 0) : z = 0 :=
begin
  unfold norm at H,
  have H1 : (2 * z.i + z.r) * (2 * z.i + z.r) = 5 * z.r * z.r,
  { suffices : 4 * (z.i * z.i + z.i * z.r - z.r * z.r) + 5 * z.r * z.r = 5 * z.r * z.r,
    { rw ← this, ring },
    simp [H] },
  have H2 : (2 * z.i + z.r).nat_abs * (2 * z.i + z.r).nat_abs = 5 * z.r.nat_abs * z.r.nat_abs,
  { have H2 := congr_arg int.nat_abs H1,
    simp [int.nat_abs_mul, -add_comm] at H2,
    exact H2 },
  suffices : (2 * z.i + z.r).nat_abs = 0 ∧ z.r.nat_abs = 0,
  { have H3 := int.eq_zero_of_nat_abs_eq_zero this.1,
    have H4 := int.eq_zero_of_nat_abs_eq_zero this.2,
    simp [H4, two_mul] at H3,
    apply ext,
    exact add_self_eq_zero.1 H3,
    exact H4 },
  generalize_hyp : (2 * z.i + z.r).nat_abs = p at H2 ⊢,
  generalize_hyp : z.r.nat_abs = q at H2 ⊢,
  clear H1 H z,
  cases nat.eq_zero_or_pos (nat.gcd p q) with h h,
  { split,
    exact nat.eq_zero_of_gcd_eq_zero_left h,
    exact nat.eq_zero_of_gcd_eq_zero_right h },
  rcases nat.exists_coprime h with ⟨m, n, co, hp, hq⟩,
  generalize_hyp : nat.gcd p q = g at h hp hq,
  have H3 : m * m = 5 * (n * n),
  { rw [hp, hq] at H2,
    apply nat.eq_of_mul_eq_mul_left (mul_pos h h),
    simpa [mul_comm, mul_left_comm, mul_assoc] using H2 },
  have H4 : nat.coprime m (n * n) := co.mul_right co,
  have H5 : nat.coprime (m * m) (n * n) := H4.mul H4,
  exfalso,
  have Hns : ∀ r, 5 ≠ r * r,
  { intro r,
    cases r, { exact dec_trivial },
    cases r, { exact dec_trivial },
    cases r, { exact dec_trivial },
    apply ne_of_lt,
    exact calc 5 < 3 * 3 : dec_trivial
      ... ≤ 3 * (r+3) : nat.mul_le_mul_left _ (nat.le_add_left _ _)
      ... ≤ (r+3) * (r+3) : nat.mul_le_mul_right _ (nat.le_add_left _ _) },
  apply Hns m,
  apply nat.dvd_antisymm,
  { rw H3, apply dvd_mul_right },
  { apply H5.dvd_of_dvd_mul_right, rw H3 }
end

theorem zero_iff_norm_zero (z : ℤα) : z = 0 ↔ norm z = 0 :=
⟨λ H, H.symm ▸ rfl, zero_of_norm_zero z⟩

theorem eq_zero_or_eq_zero_of_mul_eq_zero (z w : ℤα)
  (H : z * w = 0) : z = 0 ∨ w = 0 :=
begin
  rw [zero_iff_norm_zero, norm_mul] at H,
  rw [zero_iff_norm_zero, zero_iff_norm_zero],
  exact eq_zero_or_eq_zero_of_mul_eq_zero H
end

instance : integral_domain ℤα :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  zero_ne_one := dec_trivial,
  .. Zalpha.comm_ring }

end Zalpha
