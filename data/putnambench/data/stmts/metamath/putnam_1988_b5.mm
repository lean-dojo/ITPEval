$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_b5: the rank of the real skew-symmetric matrix of odd order
  2n+1 whose first n lower subdiagonals are 1 and whose remaining lower
  entries are -1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier 0 ..^ (2n+1) represents Fin (2*n+1). A matrix is represented
  as a real-valued function on the Cartesian square of that carrier. Thus the
  zero-based indices here are exactly the Lean indices; shifting the
  Isabelle indices 1,...,2n+1 down by one preserves their differences and
  simultaneously reindexes rows and columns.

  P88B5Minor A n k says that A has a nonzero k-by-k minor. For positive k,
  R and C select k rows and k columns, and f reindexes the selected columns
  by R; changing f can only change the determinant by a sign. P88B5Rank is
  therefore the standard largest-nonzero-minor rank specified in the source.

  The three antecedent clauses state skew-symmetry, value 1 when
  1 <= i-j <= n, and value -1 when i-j > n. The annotated source solution
  putnam_1988_b5_solution n = 2*n is inlined in the conclusion. Every
  declaration below is an unproved $a statement encoding; there is no $p
  proof declaration.
$)

$c P88B5Minor P88B5Rank $.

p88b5-minor-syntax $a wff ( P88B5Minor A n k ) $.
p88b5-rank-syntax $a wff ( P88B5Rank A n k ) $.

${
  $d A C R f i j k n $.

  p88b5-minor-definition $a |- (
    ( P88B5Minor A n k )
    <->
    (
      k = 0
      \/
      E. R e. ~P ( 0 ..^ ( ( 2 x. n ) + 1 ) )
        E. C e. ~P ( 0 ..^ ( ( 2 x. n ) + 1 ) )
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
  $d A k n $.

  p88b5-rank-definition $a |- (
    ( P88B5Rank A n k )
    <->
    (
      k e. NN0
      /\
      (
        ( P88B5Minor A n k )
        /\
        -. ( P88B5Minor A n ( k + 1 ) )
      )
    )
  ) $.
$}

${
  $d M i j n $.

  putnambench-putnam-1988-b5 $a |- A. n e. NN
    A. M e.
      (
        RR
        ^m
        (
          ( 0 ..^ ( ( 2 x. n ) + 1 ) )
          X.
          ( 0 ..^ ( ( 2 x. n ) + 1 ) )
        )
      )
      (
        (
          A. i e. ( 0 ..^ ( ( 2 x. n ) + 1 ) )
            A. j e. ( 0 ..^ ( ( 2 x. n ) + 1 ) )
              ( M ` <. i , j >. )
              =
              ( -u ( M ` <. j , i >. ) )
          /\
          (
            A. i e. ( 0 ..^ ( ( 2 x. n ) + 1 ) )
              A. j e. ( 0 ..^ ( ( 2 x. n ) + 1 ) )
                (
                  (
                    1 <_ ( i - j )
                    /\
                    ( i - j ) <_ n
                  )
                  ->
                  ( M ` <. i , j >. ) = 1
                )
            /\
            A. i e. ( 0 ..^ ( ( 2 x. n ) + 1 ) )
              A. j e. ( 0 ..^ ( ( 2 x. n ) + 1 ) )
                (
                  n < ( i - j )
                  ->
                  ( M ` <. i , j >. ) = ( -u 1 )
                )
          )
        )
        ->
        ( P88B5Rank M n ( 2 x. n ) )
      )
  $.
$}
