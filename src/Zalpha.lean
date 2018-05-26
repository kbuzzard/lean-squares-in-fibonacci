import algebra.group_power
import definitions

-- Z[alpha] where alpha := (1 + sqrt(5))/2, representing the minimal ring
-- (with addition, subtraction, and multiplication) containing the roots
-- of x^2-x-1 = 0: alpha := (1 + sqrt(5))/2 and beta (1 - sqrt(5))/2
-- (with beta < alpha)
--
-- i as in int, r as in root
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

instance : decidable_eq ℤα :=
  λ a b, if h : (a.1 = b.1 ∧ a.2 = b.2)
    then is_true (iff.mpr ext_iff h)
    else is_false (iff.mpr (by rw ext_iff) h)

instance : comm_ring ℤα :=
{ add            := (+),
  add_assoc      := by intros; apply ext; simp; simp,
  zero           := 0,
  zero_add       := by intros; apply ext; simp; simp,
  add_zero       := by intros; apply ext; simp; simp,
  neg            := has_neg.neg,
  add_left_neg   := by intros; apply ext; simp; simp,
  add_comm       := by intros; apply ext; simp; simp,
  mul            := (*),
  mul_assoc      :=
    begin
    intros, apply ext,
    simp [left_distrib, right_distrib, mul_assoc],
    simp [left_distrib, right_distrib, mul_assoc],
    end,
  one            := 1,
  one_mul        := by intros; apply ext; simp; simp,
  mul_one        := by intros; apply ext; simp; simp,
  left_distrib   :=
    begin
    intros, apply ext,
    simp [left_distrib],
    simp [left_distrib],
    end,
  right_distrib  :=
    begin
    intros, apply ext,
    simp [right_distrib],
    simp [right_distrib],
    end,
  mul_comm := by intros; apply ext; simp; simp [mul_comm],
  /-
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
    intros a b h, rw ext_iff at h, simp at h,
    by_contradiction h', -- rw [@ext_iff a, @ext_iff b] at h', simp at h',
    rw [not_or_distrib] at h',
    end
  -/
}

@[simp] lemma comm_ring_zero : comm_ring.zero ℤα = 0 := rfl

@[simp] lemma of_int_eq_coe (r : ℤ) : ↑r = of_int r :=
  eq.symm (int.eq_cast of_int rfl (λ _ _, rfl) r)
@[simp] lemma coe_int_i (r : ℤ) : (r : ℤα).i = r := by simp
@[simp] lemma coe_int_r (r : ℤ) : (r : ℤα).r = 0 := by simp

@[simp] lemma of_nat_eq_coe (r : ℕ) : ↑ r = of_nat r :=
  eq.symm (nat.eq_cast of_nat rfl rfl (λ a b, rfl) r)
@[simp] lemma coe_nat_i (r : ℕ) : (↑r : ℤα).i = r := by simp
@[simp] lemma coe_nat_r (r : ℕ) : (↑r : ℤα).r = 0 := by simp

@[simp] lemma of_fib_r (n : ℕ) : (↑ (fib n) : ℤα).r = 0 := by simp
@[simp] lemma of_fib_i (n : ℕ) : (↑ (fib n) : ℤα).i = fib n := by simp

@[simp] theorem of_int_inj {z w : ℤ} : (z : ℤα) = w ↔ z = w :=
⟨eq.substr (of_int_eq_coe z) $ eq.substr (of_int_eq_coe w) (congr_arg i), congr_arg _⟩

@[simp] theorem of_int_eq_zero {z : ℤ} : (z : ℤα) = 0 ↔ z = 0 :=
  by show (z : ℤα) = ↑ 0 ↔ z = ↑ 0; exact @of_int_inj z 0
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
  begin
  rw [int.coe_nat_add, @coe_int_add ↑a ↑b],
  end

@[simp] lemma αβsum : α + β = 1 := rfl
@[simp] lemma αβprod : α * β = -1 := rfl
lemma α_sqr : α^2 = α + 1 := rfl

theorem α_mul_right : ∀ (z : ℤα), α * z = ⟨z.r, z.i + z.r⟩ :=
  begin
  intro z, apply ext, simp, simp,
  end

theorem α_fib : ∀ (n : ℕ), α^(n+1) = ⟨Fib n, Fib (n+1)⟩ :=
  begin
  intro n, induction n with n ih,
  show α = Zalpha.mk 0 1, refl,
  show α*α^(n + 1) = ⟨Fib (n+1), Fib (n+2)⟩,
  rw ih,
  have : α * ⟨Fib n, Fib (n+1)⟩ = ⟨Fib (n+1), Fib (n+2)⟩,
  { simp [α_mul_right],
    show Fib ↑n + Fib (1 + ↑n) = Fib (2 + ↑n),
    rw [add_comm _ ↑n, add_comm _ ↑n],
    rw [← int.coe_nat_succ n],
    show Fib ↑n + Fib ↑(n+1) = Fib (↑n + 2),
    show Fib ↑n + Fib ↑(n+1) = Fib (↑n + 1 + 1),
    rw [← int.coe_nat_succ n],
    rw [← int.coe_nat_succ (nat.succ n)],
    rw [fib_down n, fib_down (n+1), fib_down (n+2)],
    rw [← int.coe_nat_add],
    apply (int.of_nat_eq_of_nat_iff (fib n + fib (n + 1)) (fib (n+2))).2,
    refl,
  },
  rw this,
  end

theorem β_mul_right : ∀ (z : ℤα), β * z = ⟨z.i - z.r, -z.i⟩ :=
  begin
  intro z, apply ext, simp, simp,
  end

-- #eval Fib (-1)
-- #eval β * β
-- #eval β * β * β * β * β

theorem β_fib : ∀ (n : ℕ), β^n = ⟨Fib (n+1), -Fib (n)⟩ :=
  begin
  intro n, induction n with n ih,
  show 1 = Zalpha.mk 1 0, refl,
  show β*β^n = ⟨Fib (n+2), -Fib ((n+1))⟩,
  rw ih,
  have : β * ⟨Fib (n+1), -Fib (n)⟩ = ⟨Fib (n+2), -Fib (n+1)⟩,
    by rw [β_mul_right, Fib.is_fib n]; simp,
  rw this,
  end

def sqrt5 : ℤα := ⟨-1, 2⟩
@[simp] lemma sqrt5_i : sqrt5.i = -1 := rfl
@[simp] lemma sqrt5_r : sqrt5.r = 2 := rfl

@[simp] lemma sqrt5_squared : sqrt5 ^ 2 = 5 := rfl

end Zalpha
