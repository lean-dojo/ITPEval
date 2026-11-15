$(
  Statement-only formalization of PutnamBench artifact putnam_1964_b4:
  for a positive finite family of distinct great circles on the unit sphere
  in real three-space, in the stated general position and with regions
  characterized by nonzero inner-product signs, the number of regions equals
  the specified solution function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P64B4R3 is real coordinate three-space, P64B4IP is its standard inner
  product, P64B4Sphere is the unit sphere, and P64B4Circle A is the
  intersection of that sphere with the plane orthogonal to A. The coordinate
  equation P64B4IP x x = 1 is equivalent to the source metric-sphere
  equation dist(x,0) = 1.

  A source SignType value is represented by its real signum value in
  { -1, 0, 1 }. Restricting the sign assignment to { -1, 1 } is exactly the
  source's pointwise nonzero condition. The answer is the published formula
  n^2 - n + 2. The final declaration is the single unproved $a corpus
  statement, and this database contains no $p proof statement.
$)

$c P64B4R3 P64B4Zero P64B4IP P64B4Sphere P64B4Circle
   $.

p64b4-space-syntax $a class P64B4R3 $.
p64b4-zero-syntax $a class P64B4Zero $.
p64b4-inner-product-syntax $a class ( P64B4IP A B ) $.
p64b4-sphere-syntax $a class P64B4Sphere $.
p64b4-circle-syntax $a class ( P64B4Circle A ) $.

p64b4-space-definition $a |- P64B4R3 = ( RR ^m ( 1 ... 3 ) ) $.

${
  p64b4-zero-definition $a |- P64B4Zero =
    ( j e. ( 1 ... 3 ) |-> 0 )
  $.
$}

${
  $d A B j $.

  p64b4-inner-product-definition $a |- (
    P64B4IP A B
  ) = (
    sum_ j e. ( 1 ... 3 )
      ( ( A ` j ) x. ( B ` j ) )
  ) $.
$}

${
  p64b4-sphere-definition $a |- P64B4Sphere = {
    x e. P64B4R3 |
      ( P64B4IP x x ) = 1
  } $.
$}

${
  $d A x $.

  p64b4-circle-definition $a |- (
    P64B4Circle A
  ) = (
    P64B4Sphere i^i
      { x e. P64B4R3 | ( P64B4IP A x ) = 0 }
  ) $.
$}

${
  $d C P R V i n s x y $.

  putnambench-putnam-1964-b4 $a |- A. n e. NN0
    A. C e. ( ( ~P P64B4R3 ) ^m ( 1 ... n ) )
      A. V e. ( P64B4R3 ^m ( 1 ... n ) )
        A. P e. ~P ( ~P P64B4R3 )
          (
            (
              (
                0 < n
                /\
                A. i e. ( 1 ... n )
                  ( C ` i ) = ( P64B4Circle ( V ` i ) )
              )
              /\
              (
                A. i e. ( 1 ... n ) ( V ` i ) =/= P64B4Zero
                /\
                C : ( 1 ... n ) -1-1-> ~P P64B4R3
              )
            )
            /\
            (
              A. x e. P64B4Sphere A. y e. P64B4Sphere
                (
                  # `
                    { i e. ( 1 ... n ) | { x , y } C_ ( C ` i ) }
                )
                <_ 2
              /\
              A. R e. ~P P64B4R3
                (
                  R e. P
                  <->
                  (
                    R =/= (/)
                    /\
                    E. s e. ( { -u 1 , 1 } ^m ( 1 ... n ) )
                      R =
                        (
                          P64B4Sphere i^i
                          {
                            x e. P64B4R3 |
                              A. i e. ( 1 ... n )
                                (
                                  sgn
                                  `
                                  (
                                    P64B4IP ( V ` i ) x
                                  )
                                )
                                =
                                ( s ` i )
                          }
                        )
                  )
                )
            )
            ->
            ( # ` P ) = ( ( ( n ^ 2 ) - n ) + 2 )
          )
  $.
$}
