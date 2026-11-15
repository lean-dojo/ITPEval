$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_a3: an odd-prime polynomial separates distinct residue
  representatives modulo the prime. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers, Prime is its class of
  natural primes, and ( 0 ..^ p ) is the residue representative set
  {0,...,p-1}. The function hypothesis gives
  F(n) = sum_(i=0)^(p-2) (i+1)n^i for every nonnegative integer n.

  The Lean and Rocq sources use {1,...,p}, another complete representative
  set modulo p. Reducing those representatives modulo p (in particular,
  sending p to 0) gives the same injectivity statement because the
  polynomial's remainder depends only on its input residue. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d F a b i n p $.

  putnambench-putnam-1983-a3 $a |- A. p e. NN0
    A. F e. ( NN0 ^m NN0 )
      (
        (
          (
            p e. Prime
            /\
            ( p mod 2 ) = 1
          )
          /\
          A. n e. NN0
            ( F ` n )
            =
            sum_ i e. ( 0 ..^ ( p - 1 ) )
              ( ( i + 1 ) x. ( n ^ i ) )
        )
        ->
        A. a e. ( 0 ..^ p )
          A. b e. ( 0 ..^ p )
            (
              a =/= b
              ->
              ( ( F ` a ) mod p ) =/= ( ( F ` b ) mod p )
            )
      )
  $.
$}
