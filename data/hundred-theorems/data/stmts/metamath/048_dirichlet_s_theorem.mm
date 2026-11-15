$(
  Statement-only formalization of Hundred Theorems item 048, Dirichlet's
  theorem on primes in arithmetic progressions.

  This is the proposition proved by set.mm theorem dirith. For a positive
  modulus N and residue A coprime to N, the primes congruent to A modulo N are
  equinumerous with the natural numbers and hence infinite.
$)

$[ library/set.mm $]

${
  $d A p $.
  $d N p $.

  hundred-theorems-048-dirichlet $a
    |- (
         ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 )
         ->
         { p e. Prime | N || ( p - A ) } ~~ NN
       )
  $.
$}
