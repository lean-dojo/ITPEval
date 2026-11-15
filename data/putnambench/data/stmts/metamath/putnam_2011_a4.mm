$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_a4: positive dimensions admitting an integer square matrix
  whose row self-dot-products are even and whose distinct-row dot-products
  are odd. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, the carrier 0 ..^ n is an n-element set corresponding to
  Fin n. The matrix A is a total integer-valued function on the Cartesian
  square of that carrier. Each displayed finite sum is exactly the dot
  product of the indicated rows.

  Membership of every row self-dot-product in Even and every distinct-row
  dot-product in Odd is therefore the source matrix condition. The annotated
  solution set {n : Nat | Odd n} is inlined as the right side of the
  biconditional. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d a i n r s $.

  putnambench-putnam-2011-a4 $a |- A. n e. NN
    (
      E. a e.
        (
          ZZ
          ^m
          ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
        )
        (
          A. r e. ( 0 ..^ n )
            (
              sum_ i e. ( 0 ..^ n )
                (
                  ( a ` <. r , i >. )
                  x.
                  ( a ` <. r , i >. )
                )
            )
            e.
            Even
          /\
          A. r e. ( 0 ..^ n )
            A. s e. ( 0 ..^ n )
              (
                r =/= s
                ->
                (
                  sum_ i e. ( 0 ..^ n )
                    (
                      ( a ` <. r , i >. )
                      x.
                      ( a ` <. s , i >. )
                    )
                )
                e.
                Odd
              )
        )
      <->
      n e. Odd
    )
  $.
$}
