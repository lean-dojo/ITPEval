$(
  Statement-only formalization of PutnamBench artifact putnam_1964_a6:
  a finite set of real points whose every nonmaximal pairwise distance is
  repeated has rational ratios between distances of distinct ordered pairs.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source set of collinear points is represented by a finite subset S of
  RR. Its auxiliary set pairs and function distance are inlined: a pair is
  <. a , b >. with a and b in S and a < b, and its distance is b - a.
  Thus ordered-pair inequality preserves the source condition q != p.

  The hypothesis says that whenever such a pair has a strictly longer pair,
  a distinct pair has the same distance. The conclusion says that the
  quotient of the distances of any two distinct pairs belongs to QQ.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c d e f S $.

  putnambench-putnam-1964-a6 $a |- A. S
    (
      (
        (
          S C_ RR
          /\
          S e. Fin
        )
        /\
        A. a e. S A. b e. S
          (
            a < b
            ->
            (
              (
                E. c e. S E. d e. S
                  (
                    c < d
                    /\
                    ( b - a ) < ( d - c )
                  )
              )
              ->
              E. e e. S E. f e. S
                (
                  e < f
                  /\
                  (
                    <. e , f >. =/= <. a , b >.
                    /\
                    ( b - a ) = ( f - e )
                  )
                )
            )
          )
      )
      ->
      A. a e. S A. b e. S A. c e. S A. d e. S
        (
          (
            (
              a < b
              /\
              c < d
            )
            /\
            <. c , d >. =/= <. a , b >.
          )
          ->
          ( ( b - a ) / ( d - c ) ) e. QQ
        )
    )
  $.
$}
