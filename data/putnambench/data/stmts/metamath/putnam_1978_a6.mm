$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_a6: fewer than twice n to the three-halves unordered pairs
  among n distinct points in the real plane are one unit apart. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The real Euclidean plane is represented isometrically by CC, with complex
  absolute value giving Euclidean distance. s ranges over arbitrary finite
  subsets of CC with positive cardinality n.

  The restricted power set consists exactly of the unordered two-element
  subsets p of s whose two distinct elements are one unit apart. Hence its
  finite cardinality is the source number of unordered unit-distance pairs.
  Since n is positive, set.mm's complex-power expression n ^c (3 / 2)
  agrees with the source real power n^(3/2).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d n p s x y $.

  putnambench-putnam-1978-a6 $a |- A. n e. NN
    A. s e. Fin
      (
        (
          s C_ CC
          /\
          ( # ` s ) = n
        )
        ->
        (
          #
          `
          {
            p e. ~P s |
              (
                ( # ` p ) = 2
                /\
                A. x e. p A. y e. p
                  (
                    x =/= y
                    ->
                    ( abs ` ( x - y ) ) = 1
                  )
              )
          }
        )
        <
        (
          2
          x.
          (
            n
            ^c
            ( 3 / 2 )
          )
        )
      )
  $.
$}
