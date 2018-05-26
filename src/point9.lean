-- 9) Deduce that if m > 2 and u m is a square, then m is a multiple of 12.

import definitions 

theorem twelve_dvd_of_fib_square (m : ℕ) :
m > 2 → (∃ d : ℕ, d ^ 2 = fib m) → 12 ∣ m := sorry

