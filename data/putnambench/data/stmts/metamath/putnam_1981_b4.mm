$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1981_b4: the assertion that every real linear subspace of five-by-
  seven matrices containing ranks zero, one, two, four, and five also
  contains rank three is false. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P81B4Rows and P81B4Cols are the Fin 5 and Fin 7 index sets, and
  P81B4Matrices is the full set of real five-by-seven matrices.

  P81B4Minor A k says that A has a nonzero k-by-k minor. The k = 0
  disjunct is the standard nonzero empty minor. For positive k, R and C
  select k rows and k columns, and f reindexes the selected columns by R;
  changing f can only change the determinant by a sign. Thus
  P81B4Rank A k is exactly the source rank definition: k is the largest
  size of a nonzero minor.

  P81B4Linear V states closure under every real linear combination r A + s B.
  The final assertion is the negation of the proposed universal implication,
  matching the source's specified solution False. All declarations are
  unproved $a statement encodings; this database contains no $p proof.
$)

$c
  P81B4Rows P81B4Cols P81B4Matrices
  P81B4Minor P81B4Rank P81B4Linear
$.

p81b4-rows-syntax $a class P81B4Rows $.
p81b4-cols-syntax $a class P81B4Cols $.
p81b4-matrices-syntax $a class P81B4Matrices $.
p81b4-minor-syntax $a wff ( P81B4Minor A k ) $.
p81b4-rank-syntax $a wff ( P81B4Rank A k ) $.
p81b4-linear-syntax $a wff ( P81B4Linear V ) $.

p81b4-rows-definition $a |- P81B4Rows = ( 0 ..^ 5 ) $.
p81b4-cols-definition $a |- P81B4Cols = ( 0 ..^ 7 ) $.
p81b4-matrices-definition $a |- P81B4Matrices =
  ( RR ^m ( P81B4Rows X. P81B4Cols ) )
$.

${
  $d A C R f i j k $.

  p81b4-minor-definition $a |- (
    ( P81B4Minor A k )
    <->
    (
      k = 0
      \/
      E. R e. ~P P81B4Rows
        E. C e. ~P P81B4Cols
          (
            (
              ( ( # ` R ) = k /\ ( # ` C ) = k )
              /\
              E. f
                (
                  f : R -1-1-onto-> C
                  /\
                  (
                    (
                      ( R maDet RRfld )
                      `
                      (
                        i e. R , j e. R |->
                          ( A ` <. i , ( f ` j ) >. )
                      )
                    )
                    =/=
                    0
                  )
                )
            )
          )
    )
  ) $.
$}

${
  $d A k $.

  p81b4-rank-definition $a |- (
    ( P81B4Rank A k )
    <->
    (
      k e. NN0
      /\
      (
        ( P81B4Minor A k )
        /\
        -. ( P81B4Minor A ( k + 1 ) )
      )
    )
  ) $.
$}

${
  $d A B V i j r s $.

  p81b4-linear-definition $a |- (
    ( P81B4Linear V )
    <->
    A. A e. V
      A. B e. V
        A. r e. RR
          A. s e. RR
            (
              i e. P81B4Rows , j e. P81B4Cols |->
                (
                  ( r x. ( A ` <. i , j >. ) )
                  +
                  ( s x. ( B ` <. i , j >. ) )
                )
            )
            e. V
  ) $.
$}

${
  $d A V $.

  putnambench-putnam-1981-b4 $a |- -.
    A. V e. ~P P81B4Matrices
      (
        (
          ( P81B4Linear V )
          /\
          (
            E. A e. V ( P81B4Rank A 0 )
            /\
            (
              E. A e. V ( P81B4Rank A 1 )
              /\
              (
                E. A e. V ( P81B4Rank A 2 )
                /\
                (
                  E. A e. V ( P81B4Rank A 4 )
                  /\
                  E. A e. V ( P81B4Rank A 5 )
                )
              )
            )
          )
        )
        ->
        E. A e. V ( P81B4Rank A 3 )
      )
  $.
$}
