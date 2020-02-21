import algebra.group_power
import data.nat.gcd
import data.nat.modeq
import number_theory.pell

attribute [elab_as_eliminator] nat.strong_induction_on
attribute [refl] dvd_refl
attribute [trans] dvd_trans
attribute [symm] nat.coprime.symm

open nat 

lemma nat.gcd_add_mul_left (a b n : ℕ) : gcd (a + b * n) b = gcd a b :=
by rw [nat.gcd_comm, gcd_rec, add_mul_mod_self_left, ← gcd_rec, nat.gcd_comm]

lemma nat.gcd_add_mul_right (a b n : ℕ) : gcd (a + n * b) b = gcd a b :=
by rw [nat.gcd_comm, gcd_rec, add_mul_mod_self_right, ← gcd_rec, nat.gcd_comm]

lemma nat.gcd_add (a b : ℕ) : gcd (a + b) b = gcd a b :=
by rw [← nat.gcd_add_mul_left a b 1, mul_one]

@[elab_as_eliminator]
lemma nat.mod_rec (m n : ℕ) {X : Sort*} {C : ℕ → X}
  (H : ∀ n, C n = C (n+m)) :
  C n = C (n%m) :=
have H1 : ∀ q r, C (r + m * q) = C r,
  from λ q, nat.rec_on q (λ r, by rw [mul_zero]; refl) $ λ n ih r,
    by rw [mul_succ, ← add_assoc, ← H, ih],
by conv in (C n) { rw [← mod_add_div n m, H1] }

def nat.mod_add (a b m : ℕ) : (a % m + b % m) % m = (a + b) % m :=
nat.modeq.modeq_add (nat.mod_mod _ _) (nat.mod_mod _ _)

-- modeq
-- needs data.nat.modeq

-- #check 2 ≡ 5 [MOD 5] -- notation

instance nonsquare_five : zsqrtd.nonsquare 5 :=
⟨λ n, nat.cases_on n dec_trivial $ λ n,
  nat.cases_on n dec_trivial $ λ n,
  nat.cases_on n dec_trivial $ λ n,
  ne_of_lt $ calc 5 < 3 * 3 : dec_trivial
    ... ≤ 3 * (n+3) : nat.mul_le_mul_left _ (nat.le_add_left _ _)
    ... ≤ (n+3) * (n+3) : nat.mul_le_mul_right _ (nat.le_add_left _ _)⟩

@[simp] lemma is_ring_hom.map_int {α : Type*} {β : Type*}
  [ring α] [ring β] (f : α → β)
  [is_ring_hom f] (i : ℤ) : f i = i :=
int.induction_on i
  (is_ring_hom.map_zero f)
  (λ j H, by simp [is_ring_hom.map_add f, is_ring_hom.map_one f, H]; exact H)
  (λ j H, by simp_rw [int.cast_sub, is_ring_hom.map_sub f, H, int.cast_one, is_ring_hom.map_one f])

@[simp] lemma units.neg_coe {α : Type*} [ring α] (x : units α) : ((-x : units α) : α) = -↑x :=
rfl
