import mathlib_someday
import tactic.ring
import data.zsqrtd.basic

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

@[ext] theorem ext : ∀ {z w : ℤα}, z.i = w.i → z.r = w.r → z = w
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

@[simp] lemma re_add_im_coe (z : ℤα) : (z.i : ℤα) + z.r * α = z :=
ext_iff.2 $ by simp

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

theorem β_mul_right (z : ℤα) : β * z = ⟨z.i - z.r, -z.i⟩ :=
by apply ext; simp

def sqrt5 : ℤα := ⟨-1, 2⟩
@[simp] lemma sqrt5_i : sqrt5.i = -1 := rfl
@[simp] lemma sqrt5_r : sqrt5.r = 2 := rfl
@[simp] lemma sqrt5_squared : sqrt5 ^ 2 = 5 := rfl

-- multiply by two, i.e. (a+bα) ↦ 2a+b(1+√5)
def to_Zsqrt5 (z : ℤα) : ℤ√5 :=
⟨2*z.i + z.r, z.r⟩

@[simp] lemma to_Zsqrt5_zero : (0:ℤα).to_Zsqrt5 = 0 := rfl

@[simp] lemma to_Zsqrt5_add (z w : ℤα) :
  (z + w).to_Zsqrt5 = z.to_Zsqrt5 + w.to_Zsqrt5 :=
by simp [to_Zsqrt5, mul_add]

@[simp] lemma to_Zsqrt5_mul (z w : ℤα) :
  (z * w).to_Zsqrt5 * 2 = z.to_Zsqrt5 * w.to_Zsqrt5 :=
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

theorem eq_zero_of_to_Zsqrt5_eq_zero (z : ℤα)
  (H : z.to_Zsqrt5 = 0) : z = 0 :=
to_Zsqrt5_inj H

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

@[simp] lemma add_conj (z : ℤα) : z + z.conj = 2 * z.i + z.r :=
by apply ext; simp [conj, two_mul]

@[simp] lemma mul_conj_eq_norm (z : ℤα) : z * z.conj = z.norm :=
by apply ext; simp [conj, norm, mul_add, mul_comm]

@[simp] lemma conj_conj (z : ℤα) : z.conj.conj = z :=
by apply ext; simp [conj]

instance : is_ring_hom conj :=
{ map_add := λ z w, by apply ext; simp [conj],
  map_mul := λ z w, by apply ext; simp [conj, add_mul, mul_add, -add_comm]; ac_refl,
  map_one := rfl }

@[simp] lemma conj_zero : (0:ℤα).conj = 0 :=
is_ring_hom.map_zero conj

lemma conj_bijective : function.bijective conj :=
⟨λ x y H, by rw [← x.conj_conj, H, y.conj_conj],
  λ x, ⟨x.conj, conj_conj x⟩⟩

lemma eq_zero_of_conj_eq_zero (z : ℤα) (H : z.conj = 0) : z = 0 :=
conj_bijective.1 H

lemma to_Zsqrt5_conj (z : ℤα) : z.conj.to_Zsqrt5 = z.to_Zsqrt5.conj :=
by rw zsqrtd.ext; split; simp [conj, to_Zsqrt5, two_mul]

lemma norm_mul (z w : ℤα) : (z * w).norm = z.norm * w.norm :=
by simp [norm, add_mul, mul_add]; ring

instance decidable_linear_ordered_comm_ring_Z_sqrt_5 :
  decidable_linear_ordered_comm_ring ℤ√5 :=
zsqrtd.decidable_linear_ordered_comm_ring

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
  zero_ne_one := dec_trivial,
  decidable_le := λ z w, show decidable (to_Zsqrt5 z ≤ to_Zsqrt5 w), by apply_instance,
  .. Zalpha.comm_ring }

lemma zero_of_norm_zero (z : ℤα) (H : z.norm = 0) : z = 0 :=
have H1 : z * z.conj = 0,
  by rw [mul_conj_eq_norm, H]; refl,
(eq_zero_or_eq_zero_of_mul_eq_zero H1).cases_on
  id z.eq_zero_of_conj_eq_zero

theorem zero_iff_norm_zero (z : ℤα) : z = 0 ↔ z.norm = 0 :=
⟨λ H, H.symm ▸ rfl, zero_of_norm_zero z⟩

instance : integral_domain ℤα := by apply_instance

theorem char_eq (z : ℤα) (H : z * z - z - 1 = 0) : z = α ∨ z = β :=
have H1 : (z - α) * (z - β) = 0,
  by rw [← H, α, β]; ring,
(eq_zero_or_eq_zero_of_mul_eq_zero H1).cases_on
  (or.inl ∘ eq_of_sub_eq_zero)
  (or.inr ∘ eq_of_sub_eq_zero)

theorem gal (f : ℤα → ℤα) [is_ring_hom f] : f = id ∨ f = conj :=
have H : f α * f α - f α - 1 = 0,
  by rw [← is_ring_hom.map_mul f, ← is_ring_hom.map_sub f];
    rw [← is_ring_hom.map_one f]; apply sub_self,
(char_eq (f α) H).cases_on
  (assume H : f α = α, or.inl $ funext $ show ∀ z, f z = z,
    from λ z, by rw [← re_add_im_coe z];
      rw [is_ring_hom.map_add f, is_ring_hom.map_mul f, H];
      rw [is_ring_hom.map_int f, is_ring_hom.map_int f])
  (assume H : f α = β, or.inr $ funext $ show ∀ z, f z = conj z,
    from λ z, by rw [← re_add_im_coe z];
      rw [is_ring_hom.map_add f, is_ring_hom.map_mul f, H];
      rw [is_ring_hom.map_int f, is_ring_hom.map_int f];
      rw [is_ring_hom.map_add conj, is_ring_hom.map_mul conj];
      rw [is_ring_hom.map_int conj, is_ring_hom.map_int conj]; refl)

namespace units

def α : units ℤα :=
⟨α, -β, rfl, rfl⟩

@[simp] lemma α_coe : (↑α : ℤα) = Zalpha.α := rfl
@[simp] lemma α_inv_coe : (↑α⁻¹ : ℤα) = -Zalpha.β := rfl

def β : units ℤα :=
⟨β, -α, rfl, rfl⟩

@[simp] lemma β_coe : (↑β : ℤα) = Zalpha.β := rfl
@[simp] lemma β_inv_coe : (↑β⁻¹ : ℤα) = -Zalpha.α := rfl

@[simp] lemma α_mul_β : α * β = -1 := rfl
@[simp] lemma β_mul_α : β * α = -1 := rfl

instance : has_repr (units ℤα) :=
⟨λ u, repr (↑u : ℤα)⟩

end units

end Zalpha
