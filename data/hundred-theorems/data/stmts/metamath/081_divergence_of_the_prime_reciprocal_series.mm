$(
  Statement-only formalization of "Divergence of the Prime Reciprocal Series"
  from Hundred Theorems corpus artifact 081: the real partial sums of the
  reciprocals of the primes tend to positive infinity. This file contains no
  proof.
$)

$[ library/set.mm $]

$(
  Every mathematical symbol below is grounded in the imported set.mm
  database. Prime is the standard class of natural prime numbers, RR and NN0
  are the real and nonnegative-integer classes, and sum_ is the finite-sum
  binder.

  For n in NN0,

    sum_ p e. ( Prime i^i ( 1 ... n ) ) ( 1 / p )

  is the sum of 1 / p over all primes p at most n. The assertion expands
  convergence to positive infinity: every real bound b is eventually a lower
  bound for every later partial sum. This is equivalent to the Lean atTop
  limit. Shifting between primes below n and primes at most n does not change
  that limit, and monotonicity of these nonnegative partial sums makes this
  formulation equivalent to the HOL Light and Isabelle nonconvergence
  statements. The final declaration is an unproved $a statement.
$)

hundred-theorems-081-prime-reciprocal-series-diverges $a
  |- A. b e. RR
       E. m e. NN0
         A. n e. NN0
           ( m <_ n ->
             b <_
               ( sum_ p e. ( Prime i^i ( 1 ... n ) ) ( 1 / p ) ) )
$.
