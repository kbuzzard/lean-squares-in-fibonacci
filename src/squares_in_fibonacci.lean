
/-
Copyright (c) 2018 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard, Kenny Lau, 

144 is the largest square in the Fibonacci sequence.
-/

/- 144 is the largest square in the Fibonacci sequence.
  Copyright Kevin Buzzard.

Authors :
  Kevin Buzzard
  Nicholas Scheel
  Kenny Lau
  Reid Barton 
  
-/

-- definition of Fibonacci sequence 
import definitions 

-- Statement of main theorem
theorem largest_square_in_fibonacci_sequence (n d : ℕ) : fib n = d ^ 2 → fib n ≤ 144 := sorry 
