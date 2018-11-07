import data.nat.prime
import data.pnat

import Reid_Barton.exactly_divides

open nat

namespace order

section raw_order

variables (p : ℕ) (hp : p > 1)

protected def order_core : Π (n : ℕ), n > 0 → {r // p^r ∣∣ n}
| 0       := λ n_pos, absurd n_pos dec_trivial
| n@(k+1) := λ n_pos,
  have n / p < n, from div_lt_self n_pos hp,
  if h : p ∣ n
  then
    have p * (n / p) = n, from nat.mul_div_cancel' h,
    let ⟨s, hs⟩ :=
      order_core (n / p)
        (pos_of_mul_pos_left (this.symm ▸ n_pos : 0 < p * (n / p)) dec_trivial)
    in ⟨succ s, this ▸ (exactly_divides_succ (hp.trans dec_trivial)).mp hs⟩
  else ⟨0, (exactly_divides_zero (hp.trans dec_trivial)).mp h⟩

def order (n : ℕ) (n_pos : n > 0) : ℕ := (order.order_core p hp n n_pos).val

lemma exactly_divides_order (n : ℕ) (n_pos : n > 0) :
  p^(order p hp n n_pos) ∣∣ n :=
(order.order_core p hp n n_pos).property


end raw_order

/- XXX comments -/

instance : has_dvd ℕ+ := ⟨λ a b, a.val ∣ b.val⟩

def 𝓟 := {p : ℕ // prime p}
notation `PP` := 𝓟

def 𝓟.gt_one (p : 𝓟) : p.val > 1 := p.property.gt_one
def 𝓟.pos (p : 𝓟) : p.val > 0 := p.property.pos

instance : has_coe 𝓟 ℕ+ := ⟨λ p, ⟨p.val, p.pos⟩⟩

def ord (p : 𝓟) (n : ℕ+) : ℕ := order p p.gt_one n n.property
def exactly_divides_ord {p : 𝓟} {n : ℕ+} : p^(ord p n) ∣∣ n :=
exactly_divides_order p p.gt_one n n.property
def exactly_divides_iff_ord {p : 𝓟} {r : ℕ} {n : ℕ+} : ord p n = r ↔ p^r ∣∣ n :=
iff.intro
  (λ e, e ▸ exactly_divides_ord)
  (exactly_divides_unique exactly_divides_ord)

variable {p : 𝓟}

-- Recursion (though we prove them in a round-about fashion)

lemma ord_not_div {n : ℕ+} : ¬(↑p ∣ n) ↔ ord p n = 0 :=
(exactly_divides_zero p.pos).trans exactly_divides_iff_ord.symm

lemma ord_div {n : ℕ+} : ord p (p * n) = succ (ord p n) :=
exactly_divides_iff_ord.mpr
((exactly_divides_succ p.pos).mp exactly_divides_ord)

-- Multiplicative

lemma ord_one : ord p 1 = 0 :=
exactly_divides_iff_ord.mpr (exactly_divides_one p.property)

lemma ord_mul (a b : ℕ+) : ord p (a * b) = ord p a + ord p b :=
exactly_divides_iff_ord.mpr
(exactly_divides_mul p.property
  exactly_divides_ord exactly_divides_ord)

lemma ord_ppow {k : ℕ} {a : ℕ+} : ord p (pnat.pow a k) = k * ord p a :=
exactly_divides_iff_ord.mpr
(exactly_divides_pow p.property exactly_divides_ord)

lemma ord_pow {k : ℕ} {a : ℕ+} : ord p (a^k) = k * ord p a := ord_ppow

-- Gcd

/-

def pgcd (a b : ℕ+) : ℕ+ := ⟨gcd a b, gcd_pos_of_pos_left b a.pos⟩

--set_option pp.notation false
@[simp] lemma pgcd_coe_something (a b : ℕ) : pgcd a b = gcd a b := begin
unfold pgcd,
--rw pnat.coe_nat_coe a, -- I am so rubbish at coe
sorry
end

--#print notation ℕ∞
lemma ord_pgcd {a b : ℕ+} : ord p (pgcd a b) = min (ord p a) (ord p b) :=
exactly_divides_iff_ord.mpr
(exactly_divides_gcd
  exactly_divides_ord exactly_divides_ord)

lemma ord_gcd {a b : ℕ+} : ord p (gcd a b) = min (ord p a) (ord p b) :=
have pgcd a b = gcd a b, from (pnat.coe_nat_coe _).symm, this ▸ ord_pgcd

instance pnat.has_le : has_le (ℕ+) := ⟨λ a b, a.1 ≤ b.1⟩

-- Addition

-- ord_mul : ∀ {p : PP} (a b : ℕ+), ord p (a * b) = ord p a + ord p b
lemma ord_le_mul_right (a b : ℕ+) : ord p a ≤ ord p (a * b) :=
begin
have H : ∀ a b c : ℕ+, a = b + c → b ≤ a := sorry,
--refine H _ _ _ (ord_mul a b) -- error
sorry
end

--set_option pp.all true
--set_option pp.notation false

lemma ord_add {a b : ℕ+} : ord p (a + b) ≥ min (ord p a) (ord p b) :=
begin
  --have H (a b : ℕ+) : gcd a b ∣ (a + b) := sorry,
  have H : ∀ (a b : ℕ+), gcd a b ∣ (a + b) :=
  λ a b, (nat.dvd_add_iff_left (gcd_dvd_right _ _)).1 (gcd_dvd_left _ _),
  rw ←ord_gcd,
  have H3 : ord p (a + b) ≥ ord p (pgcd a b) := sorry,
  have H2 := H a b,
  suffices : H3 = (ord p (a + b) ≥ ord p ↑(gcd ↑a ↑b)),
  -- now need to uncast to use H2?
  
  cases H2 with d Hd,
  /-
  Hd :
  @eq.{1} nat
    (@has_add.add.{0} nat nat.has_add
       (@coe.{1 1} pnat nat (@coe_to_lift.{1 1} pnat nat (@coe_base.{1 1} pnat nat coe_pnat_nat)) a)
       (@coe.{1 1} pnat nat (@coe_to_lift.{1 1} pnat nat (@coe_base.{1 1} pnat nat coe_pnat_nat)) b))
    (@has_mul.mul.{0} nat
       (@mul_zero_class.to_has_mul.{0} nat
          (@semiring.to_mul_zero_class.{0} nat (@comm_semiring.to_semiring.{0} nat nat.comm_semiring)))
       (nat.gcd (@coe.{1 1} pnat nat (@coe_to_lift.{1 1} pnat nat (@coe_base.{1 1} pnat nat coe_pnat_nat)) a)
          (@coe.{1 1} pnat nat (@coe_to_lift.{1 1} pnat nat (@coe_base.{1 1} pnat nat coe_pnat_nat)) b))
       d)
⊢ @ge.{0} nat nat.has_le (order.ord p (@has_add.add.{0} pnat pnat.has_add a b))
    (order.ord p
       (@coe.{1 1} nat pnat (@coe_to_lift.{1 1} nat pnat (@coe_base.{1 1} nat pnat coe_nat_pnat))
          (nat.gcd (@coe.{1 1} pnat nat (@coe_to_lift.{1 1} pnat nat (@coe_base.{1 1} pnat nat coe_pnat_nat)) a)
             (@coe.{1 1} pnat nat (@coe_to_lift.{1 1} pnat nat (@coe_base.{1 1} pnat nat coe_pnat_nat)) b))))
             -/
  change a + b = _ at Hd,
  
  --have H2 : ord p (gcd a b) ≥ min (ord p a) (ord p b),
  -- it's ord_gcd
    
  sorry,
end 
  
  #exit
  begin
    intros a b,
    refine (nat.dvd_add_iff_left _).1 _,
      exact gcd_dvd_right _ _,
    exact gcd_dvd_left _ _ -- 
  end,
sorry
end 
#check @nat.dvd_add_iff_left


-/
end order
