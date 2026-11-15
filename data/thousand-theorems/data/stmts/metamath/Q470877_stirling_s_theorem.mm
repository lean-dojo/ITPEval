$(
  Statement-only formalization of Thousand Theorems corpus artifact Q470877
  (thousand-theorems__metamath__Q470877), "Stirling's theorem": the factorial
  sequence normalized by sqrt(2 n) times (n/e)^n converges to sqrt(pi).
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  This assertion expands convergence along the natural numbers into its
  epsilon-threshold form. In SetMM, ! is factorial, _e is Euler's number,
  _pi is pi, and natural numbers are included in the real arithmetic below.
  Thus its sequence is exactly

    n |-> n! / (sqrt(2 n) * (n / e)^n),

  at every positive natural index. At n = 0, Lean's real division gives the
  source sequence value 0, whereas SetMM has ( 1 / 0 ) = (/). This difference
  does not affect convergence: in either epsilon-threshold formulation, any
  cutoff m can be replaced by max(m, 1), after which the sequence terms agree
  exactly. Thus the two convergence statements are bidirectionally equivalent.
  The declaration is the unproved corpus $a statement; this database contains
  no $p proof statement.
$)

thousand-theorems-metamath-Q470877-stirling $a
  |- A. e e. RR
       ( 0 < e ->
         E. m e. NN0
           A. n e. NN0
             ( m <_ n ->
               ( abs `
                 ( ( ( ! ` n ) /
                     ( ( sqrt ` ( 2 x. n ) ) x.
                       ( ( n / _e ) ^ n ) ) )
                   - ( sqrt ` _pi ) ) ) < e ) ) )
$.
