$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_a6: the minimum degree of a monic integer polynomial whose
  value at every integer is divisible by 10^6 is 25. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  A polynomial of degree d is represented by its complete integer
  coefficient function A on NN0: its coefficient at d is one, and every
  coefficient above d is zero. Its value at x is the finite coefficient
  sum through d. Thus this representation ranges over exactly the monic
  integer polynomials of degree d.

  The first conjunct gives an internal degree-25 witness. The second
  excludes an internal witness at every smaller nonnegative degree, which
  is equivalent to the source minimum-degree statement. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d A d i x $.

  putnambench-putnam-1974-a6 $a |- (
    E. A e. ( ZZ ^m NN0 )
      (
        ( A ` ( 5 x. 5 ) ) = 1
        /\
        (
          A. i e. NN0
            (
              ( 5 x. 5 ) < i
              ->
              ( A ` i ) = 0
            )
          /\
          A. x e. ZZ
            (
              ( ( 9 + 1 ) ^ 6 )
              ||
              sum_ i e. ( 0 ... ( 5 x. 5 ) )
                ( ( A ` i ) x. ( x ^ i ) )
            )
        )
      )
    /\
    A. d e. NN0
      (
        d < ( 5 x. 5 )
        ->
        -. E. A e. ( ZZ ^m NN0 )
          (
            ( A ` d ) = 1
            /\
            (
              A. i e. NN0
                (
                  d < i
                  ->
                  ( A ` i ) = 0
                )
              /\
              A. x e. ZZ
                (
                  ( ( 9 + 1 ) ^ 6 )
                  ||
                  sum_ i e. ( 0 ... d )
                    ( ( A ` i ) x. ( x ^ i ) )
                )
            )
          )
      )
  ) $.
$}
