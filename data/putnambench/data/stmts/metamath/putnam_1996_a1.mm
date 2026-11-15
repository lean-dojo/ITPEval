$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_a1: the least area of a positive rectangle satisfying the
  stated max/min packing inequalities for every positive real pair whose
  squared lengths sum to one is (1 + sqrt 2) / 2. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P96A1Property A is definitionally the source predicate Aprop A. The four
  side variables remain arbitrary reals, the rectangle sides remain internal
  existential witnesses, and the if-expressions are the real maximum and
  minimum functions. The final conjunction states both feasibility at the
  displayed area and its minimality among every real A satisfying the same
  property.

  All declarations below are unproved $a statement encodings; this database
  contains no $p proof statement.
$)

$c P96A1Property $.

p96a1-property-syntax $a wff ( P96A1Property A ) $.

${
  $d A a b x y $.

  p96a1-property-definition $a |- (
    ( P96A1Property A )
    <->
    A. x e. RR
      A. y e. RR
        (
          (
            (
              0 < x
              /\
              0 < y
            )
            /\
            ( ( x ^ 2 ) + ( y ^ 2 ) ) = 1
          )
          ->
          E. a e. RR
            E. b e. RR
              (
                (
                  (
                    0 < a
                    /\
                    0 < b
                  )
                  /\
                  ( a x. b ) = A
                )
                /\
                (
                  ( x + y )
                  <_
                  if ( a <_ b , b , a )
                  /\
                  if ( x <_ y , y , x )
                  <_
                  if ( a <_ b , a , b )
                )
              )
        )
  ) $.
$}

putnambench-putnam-1996-a1 $a |- (
  (
    P96A1Property
      ( ( 1 + ( sqrt ` 2 ) ) / 2 )
  )
  /\
  A. A e. RR
    (
      ( P96A1Property A )
      ->
      ( ( 1 + ( sqrt ` 2 ) ) / 2 ) <_ A
    )
) $.
