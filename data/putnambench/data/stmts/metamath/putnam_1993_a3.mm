$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_a3: the number of intersection-to-minimum preserving maps from
  the power set of an n-element set to an m-element chain is the sum of the
  nth powers of the integers from 1 through m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive natural n and m, ~P ( 1 ... n ) is the full power set of an
  n-element set, and ( 1 ... m ) ^m ~P ( 1 ... n ) is the class of all total
  functions from that power set to the m-element chain.

  For natural-valued f, the two order implications in the restricted class
  are equivalent to

    f ( A intersection B ) = min ( f A , f B ).

  Thus the left side is exactly the source count c(n,m), with its defining
  equation substituted into the conclusion. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d A B f j m n $.

  putnambench-putnam-1993-a3 $a |- A. n e. NN A. m e. NN
    (
      #
      `
      {
        f e.
          (
            ( 1 ... m )
            ^m
            ( ~P ( 1 ... n ) )
          )
        |
        A. A e. ( ~P ( 1 ... n ) )
          A. B e. ( ~P ( 1 ... n ) )
            (
              (
                ( f ` A ) <_ ( f ` B )
                ->
                ( f ` ( A i^i B ) ) = ( f ` A )
              )
              /\
              (
                ( f ` B ) <_ ( f ` A )
                ->
                ( f ` ( A i^i B ) ) = ( f ` B )
              )
            )
      }
      =
      sum_ j e. ( 1 ... m ) ( j ^ n )
    )
  $.
$}
