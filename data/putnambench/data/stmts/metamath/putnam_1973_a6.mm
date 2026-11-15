$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_a6: impossibility of seven distinct real affine lines having
  at least six points incident with exactly three lines and at least four
  points incident with exactly two lines. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal 7 is the index set {0,...,6}, and a member L of
  ( RR X. RR ) ^m 7 assigns to each index a real slope/intercept pair.
  P73A6Points n L is the set of real-plane points for which there is a
  unique subset S of the seven indices having cardinality n such that the
  point lies on every line indexed by S. For n = 2 or n = 3 this is
  equivalent to incidence with exactly n of the seven lines.

  The final assertion negates the existence of a pairwise distinct family
  satisfying both source cardinality lower bounds. Every declaration is an
  unproved $a statement; this database contains no $p proof statement.
$)

$c P73A6Points $.

p73a6-points-syntax $a class ( n P73A6Points L ) $.

${
  $d L S i n p $.

  p73a6-points-definition $a |- (
    n P73A6Points L
  ) = {
    p e. ( RR X. RR ) |
      E! S e. ~P 7
        (
          ( # ` S ) = n
          /\
          A. i e. S
            (
              ( 2nd ` p )
              =
              (
                (
                  ( 1st ` ( L ` i ) )
                  x.
                  ( 1st ` p )
                )
                +
                ( 2nd ` ( L ` i ) )
              )
            )
        )
  } $.
$}

${
  $d L i j $.

  putnambench-putnam-1973-a6 $a |- -.
    E. L e. ( ( RR X. RR ) ^m 7 )
      (
        A. i e. 7 A. j e. 7
          (
            i =/= j
            ->
            ( L ` i ) =/= ( L ` j )
          )
        /\
        (
          6 <_ ( # ` ( 3 P73A6Points L ) )
          /\
          4 <_ ( # ` ( 2 P73A6Points L ) )
        )
      )
  $.
$}
