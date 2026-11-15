$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_b4: the greatest number of vertices of the Boolean n-cube
  contained in a k-dimensional real linear subspace is 2^k. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite ordinal 0..^n indexes the coordinates of the generalized real
  Euclidean vector space RR^ ` (0..^n). P06B4Cube(n) is its subset of
  functions whose every coordinate is either 0 or 1.

  The source's IsGreatest conclusion is expanded into the equivalent
  conjunction of attainment and a universal upper bound over all
  k-dimensional linear subspaces. The source parameter Z and its defining
  equality are eliminated by direct substitution of P06B4Cube(n). Every $a
  declaration is an unproved statement encoding; this database contains no
  $p proof declaration.
$)

$c P06B4Cube $.

p06b4-cube-syntax $a class P06B4Cube $.

${
  $d i n x $.

  p06b4-cube-definition $a |- P06B4Cube =
    ( n e. NN |->
      {
        x e. ( RR ^m ( 0 ..^ n ) ) |
          A. i e. ( 0 ..^ n )
            (
              ( x ` i ) = 0
              \/
              ( x ` i ) = 1
            )
      }
    )
  $.
$}

${
  $d V k n $.

  putnambench-putnam-2006-b4 $a |-
    A. n e. NN A. k e. NN0
      (
        k <_ n
        ->
        (
          E. V e. ( LSubSp ` ( RR^ ` ( 0 ..^ n ) ) )
            (
              (
                dim
                `
                ( ( RR^ ` ( 0 ..^ n ) ) |`s V )
              )
              =
              k
              /\
              (
                #
                `
                ( ( P06B4Cube ` n ) i^i V )
              )
              =
              ( 2 ^ k )
            )
          /\
          A. V e. ( LSubSp ` ( RR^ ` ( 0 ..^ n ) ) )
            (
              (
                dim
                `
                ( ( RR^ ` ( 0 ..^ n ) ) |`s V )
              )
              =
              k
              ->
              (
                #
                `
                ( ( P06B4Cube ` n ) i^i V )
              )
              <_
              ( 2 ^ k )
            )
        )
      )
  $.
$}
