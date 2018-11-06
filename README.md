# lean-squares-in-fibonacci
144 is the largest square in the Fibonacci sequence

### Overview of repo

The proof follows Cohn's original 1963 proof. In 2017nt2.pdf I break the argument up into 12 points. The files "pointX.lean" pertain to point X of the pdf. On top of that, definitions.lean is the basic Fibonacci definitions; "Fib" is the definition using Z[alpha] (and there are two implementations of this -- one using an abstract ring in Zalpha.lean and one using the reals in Zalpha_real.lean) and "fib" the standard recursive definition. 

What needs doing? There are some sorries in point1, and some points are missing completely.
