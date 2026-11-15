$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_b1: an even square grid with row-major integer labels and
  balanced binary colors in every row and column has equal color-class sums.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, the half-open interval 0 ..^ n is the n-element carrier
  corresponding to Fin n. A and C are arbitrary curried total functions on
  the full n by n grid, with integer labels and binary colors respectively.
  The label equation is the source row-major enumeration k*n+l+1.

  The row and column cardinalities are exactly the source sums of zero-color
  indicators. Since 2 divides n, the field quotient n/2 equals the natural
  half used by the Lean and Isabelle statements. The two nested finite sums
  are precisely the sums of labels on colors 0 and 1.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A C k l n $.

  putnambench-putnam-2001-b1 $a |- A. n e. NN
    A. A e.
      (
        ( ZZ ^m ( 0 ..^ n ) )
        ^m
        ( 0 ..^ n )
      )
      A. C e.
        (
          (
            ( 0 ..^ 2 )
            ^m
            ( 0 ..^ n )
          )
          ^m
          ( 0 ..^ n )
        )
        (
          (
            2 || n
            /\
            (
              A. k e. ( 0 ..^ n )
                A. l e. ( 0 ..^ n )
                  (
                    ( ( A ` k ) ` l )
                    =
                    ( ( k x. n ) + ( l + 1 ) )
                  )
              /\
              (
                A. k e. ( 0 ..^ n )
                  (
                    #
                    `
                    {
                      l e. ( 0 ..^ n ) |
                      ( ( C ` k ) ` l ) = 0
                    }
                  )
                  =
                  ( n / 2 )
                /\
                A. l e. ( 0 ..^ n )
                  (
                    #
                    `
                    {
                      k e. ( 0 ..^ n ) |
                      ( ( C ` k ) ` l ) = 0
                    }
                  )
                  =
                  ( n / 2 )
              )
            )
          )
          ->
          (
            sum_ k e. ( 0 ..^ n )
              sum_ l e. ( 0 ..^ n )
                if (
                  ( ( C ` k ) ` l ) = 0 ,
                  ( ( A ` k ) ` l ) ,
                  0
                )
          )
          =
          (
            sum_ k e. ( 0 ..^ n )
              sum_ l e. ( 0 ..^ n )
                if (
                  ( ( C ` k ) ` l ) = 1 ,
                  ( ( A ` k ) ` l ) ,
                  0
                )
          )
        )
  $.
$}
