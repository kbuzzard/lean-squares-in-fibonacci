# lean-squares-in-fibonacci
144 is the largest square in the Fibonacci sequence

### Overview of repo

The proof follows Cohn's original 1963 proof. In 2017nt2.pdf I break the argument up into 12 points. The files "pointX.lean" pertain to point X of the pdf. On top of that, definitions.lean is the basic Fibonacci definitions; "Fib" is the definition using Z[alpha] (and there are two implementations of this -- one using an abstract ring in Zalpha.lean and one using the reals in Zalpha_real.lean) and "fib" the standard recursive definition. 

What needs doing? There are some sorries in point1, and some points are missing completely.

### Details

`for_mathlib` contains a couple of files written by Reid Barton
about "exact divisibility", i.e. the valuation function v_p (p prime)
sending an integer n to the number of times p occurs in the prime
factorization of n. This was written in 2017 or 2018 and is now
almost certainly in mathlib (e.g. in Rob Lewis' work on the p-adic
numbers). Note that these files are not imported by the rest of the
repo.

`mathlib_someday` contains a few lemmas about naturals, and also
the instance `nonsquare_five : zsqrtd.nonsquare 5`, proving that
5 isn't a square(!) (nobody has coded up the algorithm to check
whether a given natural number is a square or not, so a hands-on
proof needed to be given).

`Zalpha` sets up the basic theory of the ring of integers of
Q(sqrt(5)), namely Z[(1+sqrt(5))/2] (notation `ℤα`).

`Zalpha_real` sets up the theory of the embedding from ℤα to ℝ
and proves various irrationality results. 

`real_alpha` does essentially nothing and is probably unused.

`definitions` sets up the basic definitions of Fibonacci and Lucas
numbers, and relates them to `α` and `β`.

`fib_mod` proves various results about the Fibonacci sequence
modulo 16 and other numbers.

`squares_in_fibonacci` contains a statement of the main theorem.

`pointX` are the proofs of the various points in the pdf.
