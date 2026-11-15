$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_b1: any two partitions of a nine-element set have two distinct
  elements whose containing blocks have equal sizes in both partitions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier ( 1 ... 9 ) is the canonical nine-element set from the problem
  statement. Each partition is a family of nonempty subsets whose union is
  the carrier and whose distinct members are disjoint. The existentially
  selected blocks A, B, C, and D contain x and y in the first and second
  partitions respectively, so their finite cardinalities are exactly the
  two source block-size values.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A B C D P Q x y $.

  putnambench-putnam-1995-b1 $a |-
    A. P e. ~P ( ~P ( 1 ... 9 ) )
      A. Q e. ~P ( ~P ( 1 ... 9 ) )
        (
          (
            (
              (
                A. A e. P A =/= (/)
                /\
                U. P = ( 1 ... 9 )
              )
              /\
              A. A e. P A. B e. P
                (
                  A =/= B
                  ->
                  ( A i^i B ) = (/)
                )
            )
            /\
            (
              (
                A. C e. Q C =/= (/)
                /\
                U. Q = ( 1 ... 9 )
              )
              /\
              A. C e. Q A. D e. Q
                (
                  C =/= D
                  ->
                  ( C i^i D ) = (/)
                )
            )
          )
          ->
          E. x e. ( 1 ... 9 ) E. y e. ( 1 ... 9 )
            (
              x =/= y
              /\
              E. A e. P E. B e. P E. C e. Q E. D e. Q
                (
                  (
                    x e. A
                    /\
                    y e. B
                  )
                  /\
                  (
                    (
                      x e. C
                      /\
                      y e. D
                    )
                    /\
                    (
                      ( # ` A ) = ( # ` B )
                      /\
                      ( # ` C ) = ( # ` D )
                    )
                  )
                )
            )
        )
  $.
$}
