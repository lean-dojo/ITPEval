$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_b4: the ordered composition of equal-angle rotations about the
  points 1 through n translates every complex point by n. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The natural number n remains in NN0 with the explicit assumption n >= 2.
  The family R ranges over all NN0-indexed complex self-maps. Its initial
  value is the identity, and the displayed pointwise recurrence is exactly
  R_(k+1) = Rk_(k+1) composed with R_k after the source definition

    Rk_j(Q) = j + exp(i * 2 * pi / n) * (Q - j)

  is substituted. Thus the auxiliary family Rk is eliminated definitionally,
  while the universal quantification over R and every complex input is
  preserved. Equality of the resulting complex self-maps is expressed
  pointwise, equivalently to the function equality in the ground truth.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d R k n z $.

  putnambench-putnam-2004-b4 $a |-
    A. n e. NN0
      (
        2 <_ n
        ->
        A. R e. ( ( CC ^m CC ) ^m NN0 )
          (
            (
              A. z e. CC
                ( ( R ` 0 ) ` z ) = z
              /\
              A. k e. NN0 A. z e. CC
                ( ( R ` ( k + 1 ) ) ` z )
                =
                (
                  ( k + 1 )
                  +
                  (
                    (
                      exp
                      `
                      (
                        ( ( _i x. 2 ) x. _pi )
                        /
                        n
                      )
                    )
                    x.
                    (
                      ( ( R ` k ) ` z )
                      -
                      ( k + 1 )
                    )
                  )
                )
            )
            ->
            A. z e. CC
              ( ( R ` n ) ` z ) = ( z + n )
          )
      )
  $.
$}
