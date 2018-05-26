import definitions Zalpha

open Zalpha

theorem fib_αβ : ∀ (m : ℕ), ↑(fib m) * sqrt5 = α^m - β^m :=
  begin
  intro m,
  cases m, refl,
  rw [α_fib m, β_fib (m+1)],
  apply ext,
  {
    simp,
    have : (1 + (1 + (m : ℤ))) = ↑(m+1+1), simp,
    rw [this, fib_down (m+2), fib_down m],
    apply eq_add_of_add_neg_eq, rw [← eq_neg_add_iff_add_eq],
    simp, rw [← int.coe_nat_add, int.coe_nat_eq_coe_nat_iff],
    refl,
  },
  {
    simp,
    have : Fib (1 + ↑m) = ↑(fib (m + 1)),
      {
        show Fib (↑1 + ↑m) = fib (m + 1),
        rw [← @int.coe_nat_add 1 m, add_comm, fib_down (m+1)]
      },
    rw [this, mul_two],
  },
  end

theorem luc_αβ : ∀ (m : ℕ), ↑(luc m) = α^m + β^m :=
  begin
  intro m,
  cases m, refl,
  rw [α_fib m, β_fib (m+1)],
  apply ext,
  {
    simp,
    have : (1 + (1 + (m : ℤ))) = ↑(m+1+1), simp,
    rw [this, fib_down (m+2), fib_down m],
    rw [← int.coe_nat_add, int.coe_nat_eq_coe_nat_iff],
    show luc (m+1) = fib m + fib (m + 2),
    induction m using nat.rec_on_two with n h0 h1, refl, refl,
    simp at h0, simp at h1,
    unfold1 luc, rw [h0, h1], simp,
    show
      fib n + (fib (n + 1) + (fib (n + 2) + fib (n + 3))) =
      fib (n + 2) + fib (n + 4),
    rw [← add_assoc], refl,
  },
  simp, -- trivial! this is since (α^m).r = -(β^m).r
  end
