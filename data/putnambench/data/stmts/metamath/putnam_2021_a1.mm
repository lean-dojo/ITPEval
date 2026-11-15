$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_a1: the least number of length-five hops on the integer
  lattice from (0,0) to (2021,2021) is 578. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P21A1Path k says that two integer-valued coordinate functions on the
  inclusive index interval 0 ... k start at the origin, end at
  (2021,2021), and have squared displacement 25 at every successive index.
  Pairing the coordinate values at each index is definitionally equivalent
  to the source's list of integer-coordinate points with its Chain'
  condition, and k is exactly the number of hops.

  The final conjunction expands IsLeast: a path with 578 hops exists, and
  every nonnegative number of hops admitting such a path is at least 578.
  All declarations are unproved $a statement encodings; this database
  contains no $p proof statement.
$)

$c P21A1Path $.

p21a1-path-syntax $a wff ( P21A1Path k ) $.

${
  $d i k x y $.

  p21a1-path-definition $a |- (
    ( P21A1Path k )
    <->
    E. x e. ( ZZ ^m ( 0 ... k ) )
      E. y e. ( ZZ ^m ( 0 ... k ) )
        (
          (
            ( x ` 0 ) = 0
            /\
            ( y ` 0 ) = 0
          )
          /\
          (
            (
              ( x ` k ) = ( ; ; ; 2 0 2 1 )
              /\
              ( y ` k ) = ( ; ; ; 2 0 2 1 )
            )
            /\
            A. i e. ( 1 ... k )
              (
                (
                  (
                    ( x ` i )
                    -
                    ( x ` ( i - 1 ) )
                  )
                  ^
                  2
                )
                +
                (
                  (
                    ( y ` i )
                    -
                    ( y ` ( i - 1 ) )
                  )
                  ^
                  2
                )
              )
              =
              ( ; 2 5 )
          )
        )
  ) $.
$}

putnambench-putnam-2021-a1 $a |- (
  ( P21A1Path ( ; ; 5 7 8 ) )
  /\
  A. k e. NN0
    (
      ( P21A1Path k )
      ->
      ( ; ; 5 7 8 ) <_ k
    )
) $.
