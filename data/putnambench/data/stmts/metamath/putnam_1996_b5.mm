$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_b5: the number of length-n sign strings whose every consecutive
  substring has signed sum between negative two and two. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal interval 0 ..^ n is the n-element carrier representing Fin n,
  and { -u 1 , 1 } is the integer-unit codomain representing the symbols O
  and X. For endpoints a <= b, the inclusive interval a ... b and the finite
  sum give exactly the source value Delta(S[a..b]).

  The restricted class therefore contains exactly the balanced strings from
  the Lean source. It is also in bijection with the Isabelle representation
  by extending each finite string with False outside 0 ..^ n. The right-hand
  side is the resolved closed form recorded in the Lean annotation and stated
  explicitly in the Rocq source. The final declaration is an unproved $a
  statement, and this database contains no $p proof statement.
$)

${
  $d a b i n s $.

  putnambench-putnam-1996-b5 $a |- A. n e. NN0
    (
      #
      `
      {
        s e. ( { -u 1 , 1 } ^m ( 0 ..^ n ) ) |
        A. a e. ( 0 ..^ n ) A. b e. ( 0 ..^ n )
          (
            a <_ b
            ->
            (
              ( -u 2 )
              <_
              sum_ i e. ( a ... b ) ( s ` i )
              /\
              (
                sum_ i e. ( a ... b ) ( s ` i )
              )
              <_
              2
            )
          )
      }
    )
    =
    (
      (
        ( 2 ^ ( |_ ` ( ( n + 2 ) / 2 ) ) )
        +
        ( 2 ^ ( |_ ` ( ( n + 1 ) / 2 ) ) )
      )
      -
      2
    )
  $.
$}
