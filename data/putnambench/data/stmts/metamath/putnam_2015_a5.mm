$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_a5: parity of the number of positive integers below one
  quarter of an odd positive integer and coprime to it, characterized by
  prime powers in residue classes five or seven modulo eight. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN, NN0, Prime, and Odd are SetMM's classes of positive naturals,
  nonnegative naturals, natural primes, and odd integers. Restricting a to
  NN is exactly the source condition 0 < a. The remaining strict inequality
  and gcd equality define the source set, and # is its finite cardinality.

  Quantifying q over NN incorporates the source positivity assumption;
  oddness and the defining equality for Nq remain explicit hypotheses.
  The prime p and positive exponent k remain internally existentially
  quantified. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d N a k p q $.

  putnambench-putnam-2015-a5 $a |-
    A. q e. NN A. N e. NN0
      (
        (
          q e. Odd
          /\
          N
          =
          (
            #
            `
            {
              a e. NN |
              (
                a < ( q / 4 )
                /\
                ( a gcd q ) = 1
              )
            }
          )
        )
        ->
        (
          N e. Odd
          <->
          E. p e. Prime E. k e. NN
            (
              q = ( p ^ k )
              /\
              (
                ( p mod 8 ) = 5
                \/
                ( p mod 8 ) = 7
              )
            )
        )
      )
  $.
$}
