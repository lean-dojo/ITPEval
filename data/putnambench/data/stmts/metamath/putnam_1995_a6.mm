$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_a6: for some number of columns at least 1995, three-row
  matrices whose columns are permutations of 1, 2, 3 yield consecutive
  row sums at least four times as often as three equal row sums. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P95A6Matrices n is the full set of integer-valued matrices indexed by
  ( 0 ..^ 3 ) X. ( 0 ..^ n ), the SetMM carriers corresponding to
  Fin 3 and Fin n. P95A6Valid n retains exactly those matrices for which
  the set of the three entries in every column is { 1, 2, 3 }; because
  that set has three distinct elements, each column is a permutation.

  P95A6RowSums n M is the set of the three integer row sums, so repeated
  row sums are collapsed exactly as in the source Set-valued definition.
  P95A6Progression is the source three-element consecutive-integer
  predicate, with all witnesses still internally existential. Inlining
  these definitions is definitionally equivalent to quantifying the
  source helper objects together with their defining equalities.

  The final assertion preserves the existential natural n, the lower bound
  n >= 1995, and the cardinality comparison between the two subsets of
  valid matrices. Every declaration is an unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c P95A6Matrices P95A6Valid P95A6RowSums P95A6Progression $.

p95a6-matrices-syntax $a class P95A6Matrices $.
p95a6-valid-syntax $a class P95A6Valid $.
p95a6-row-sums-syntax $a class P95A6RowSums $.
p95a6-progression-syntax $a wff ( P95A6Progression S ) $.

${
  p95a6-matrices-definition $a |- P95A6Matrices =
    ( n e. NN0 |->
      (
        ZZ
        ^m
        (
          ( 0 ..^ 3 )
          X.
          ( 0 ..^ n )
        )
      )
    )
  $.
$}

${
  $d M j n $.

  p95a6-valid-definition $a |- P95A6Valid =
    ( n e. NN0 |->
      {
        M e. ( P95A6Matrices ` n ) |
        A. j e. ( 0 ..^ n )
          {
            ( M ` <. 0 , j >. ) ,
            ( M ` <. 1 , j >. ) ,
            ( M ` <. 2 , j >. )
          }
          =
          { 1 , 2 , 3 }
      }
    )
  $.
$}

${
  $d M i j n z $.

  p95a6-row-sums-definition $a |- P95A6RowSums =
    ( n e. NN0 |->
      (
        M e. ( P95A6Matrices ` n ) |->
          {
            z e. ZZ |
            E. i e. ( 0 ..^ 3 )
              z =
              (
                sum_ j e. ( 0 ..^ n )
                  ( M ` <. i , j >. )
              )
          }
      )
    )
  $.
$}

${
  $d S a b c $.

  p95a6-progression-definition $a |- (
    ( P95A6Progression S )
    <->
    (
      ( # ` S ) = 3
      /\
      E. a e. ZZ
        E. b e. ZZ
          E. c e. ZZ
            (
              { a , b , c } = S
              /\
              (
                b = ( a + 1 )
                /\
                c = ( a + 2 )
              )
            )
    )
  ) $.
$}

${
  $d M n $.

  putnambench-putnam-1995-a6 $a |-
    E. n e. NN0
      (
        ; ; ; 1 9 9 5 <_ n
        /\
        (
          4
          x.
          (
            #
            `
            {
              M e. ( P95A6Valid ` n ) |
              (
                #
                `
                (
                  ( P95A6RowSums ` n )
                  `
                  M
                )
              )
              =
              1
            }
          )
        )
        <_
        (
          #
          `
          {
            M e. ( P95A6Valid ` n ) |
            (
              P95A6Progression
              (
                ( P95A6RowSums ` n )
                `
                M
              )
            )
          }
        )
      )
  $.
$}
