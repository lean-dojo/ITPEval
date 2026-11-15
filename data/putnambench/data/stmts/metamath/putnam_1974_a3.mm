$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_a3: primes represented by x^2 + 16y^2 and by
  4x^2 + 4xy + 5y^2 are characterized by their residue classes modulo
  eight. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ZZ are the SetMM classes of nonnegative integers and integers,
  and Prime is its class of natural primes. The antecedent is the supplied
  sum-of-two-squares characterization, with its integer witnesses internally
  existentially quantified. The first and second right-hand sides inline the
  two solution sets specified by the ground-truth sources: primes congruent
  to one and five modulo eight, respectively.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d m n p x y $.

  putnambench-putnam-1974-a3 $a |- (
    (
      A. p e. NN0
        (
          (
            p e. Prime
            /\
            2 < p
          )
          ->
          (
            E. m e. ZZ E. n e. ZZ
              p = ( ( m ^ 2 ) + ( n ^ 2 ) )
            <->
            ( p mod 4 ) = 1
          )
        )
    )
    ->
    A. p e. NN0
      (
        (
          (
            (
              p e. Prime
              /\
              2 < p
            )
            /\
            E. x e. ZZ E. y e. ZZ
              p =
                (
                  ( x ^ 2 )
                  +
                  ( ( 9 + 7 ) x. ( y ^ 2 ) )
                )
          )
          <->
          (
            p e. Prime
            /\
            ( p mod 8 ) = 1
          )
        )
        /\
        (
          (
            (
              p e. Prime
              /\
              2 < p
            )
            /\
            E. x e. ZZ E. y e. ZZ
              p =
                (
                  (
                    ( 4 x. ( x ^ 2 ) )
                    +
                    ( ( 4 x. x ) x. y )
                  )
                  +
                  ( 5 x. ( y ^ 2 ) )
                )
          )
          <->
          (
            p e. Prime
            /\
            ( p mod 8 ) = 5
          )
        )
      )
  ) $.
$}
