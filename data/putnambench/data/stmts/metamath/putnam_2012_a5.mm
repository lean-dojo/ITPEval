$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_a5: classification of positive dimensions and prime field
  sizes admitting an affine map whose first p^n iterates of zero are all
  distinct. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, the carrier 0 ..^ n is the n-element set corresponding
  to Fin n. P12A5Vectors n F is the full set of vectors over the field F,
  and Base ` ((0 ..^ n) Mat F) is the full set of n by n matrices over F.
  P12A5Affine n F M v is definitionally the map x |-> v + Mx, with matrix
  multiplication expanded as a finite sum in F.

  F remains an arbitrary finite field of cardinality p. IterComp is SetMM's
  native finite-iteration operator, and the map on 1 ... p^n sends k to the
  k-fold iterate of the affine map at the zero vector. Requiring this map to
  be one-to-one is exactly pairwise distinctness of those p^n vectors.

  The right side inlines the ground-truth solution set: n = 1 for arbitrary
  prime p, together with the exceptional pair n = p = 2. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

$c P12A5Vectors P12A5Affine $.

p12a5-vectors-syntax $a class ( P12A5Vectors n F ) $.
p12a5-affine-syntax $a class ( P12A5Affine n F M v ) $.

${
  p12a5-vectors-definition $a |- ( P12A5Vectors n F ) =
    (
      ( Base ` F )
      ^m
      ( 0 ..^ n )
    )
  $.
$}

${
  $d F M j n r v x $.

  p12a5-affine-definition $a |- ( P12A5Affine n F M v ) =
    (
      x e. ( P12A5Vectors n F ) |->
        (
          r e. ( 0 ..^ n ) |->
            (
              ( v ` r )
              ( +g ` F )
              (
                F
                gsum
                (
                  j e. ( 0 ..^ n ) |->
                    (
                      ( r M j )
                      ( .r ` F )
                      ( x ` j )
                    )
                )
              )
            )
        )
    )
  $.
$}

${
  $d F M k n p r v $.

  putnambench-putnam-2012-a5 $a |-
    A. n e. NN
      A. p e. Prime
        A. F
          (
            (
              F e. Field
              /\
              (
                ( Base ` F ) e. Fin
                /\
                ( # ` ( Base ` F ) ) = p
              )
            )
            ->
            (
              (
                E. M e. ( Base ` ( ( 0 ..^ n ) Mat F ) )
                  E. v e. ( P12A5Vectors n F )
                    (
                      k e. ( 1 ... ( p ^ n ) ) |->
                        (
                          (
                            (
                              IterComp
                              `
                              ( P12A5Affine n F M v )
                            )
                            `
                            k
                          )
                          `
                          (
                            r e. ( 0 ..^ n ) |->
                              ( 0g ` F )
                          )
                        )
                    )
                    :
                    ( 1 ... ( p ^ n ) )
                    -1-1->
                    ( P12A5Vectors n F )
              )
              <->
              (
                n = 1
                \/
                (
                  n = 2
                  /\
                  p = 2
                )
              )
            )
          )
  $.
$}
