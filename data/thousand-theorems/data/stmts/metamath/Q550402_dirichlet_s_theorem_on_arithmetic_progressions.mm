$(
  Statement-only formalization of Thousand Theorems corpus artifact Q550402
  (thousand-theorems__metamath__Q550402), "Dirichlet's theorem on arithmetic
  progressions": for a positive modulus and an invertible residue class, the
  set of natural primes in that residue class is infinite. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN is SetMM's class of positive integers, so q e. NN exactly represents a
  natural modulus equipped with Lean's NeZero q instance. The half-open
  interval ( 0 ..^ q ) is a bijective set of representatives for ZMod q.
  For such a representative a, ( a gcd q ) = 1 is equivalent to IsUnit a,
  and equality of p mod q with a is equality after casting p into ZMod q.

  Fin is SetMM's class of finite sets. Thus non-membership in Fin of the
  displayed set of primes is exactly the source Set.Infinite conclusion.
  The final declaration is the single unproved $a corpus statement; this
  root file contains no $p proof statement.
$)

${
  $d a p q $.

  thousand-theorems-q550402-dirichlets-theorem-on-arithmetic-progressions $a
    |- A. q e. NN
         A. a e. ( 0 ..^ q )
           (
             ( a gcd q ) = 1
             ->
             -. { p e. Prime | ( p mod q ) = a } e. Fin
           )
  $.
$}
