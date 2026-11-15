$(
  Statement-only formalization of PutnamBench artifact putnam_1962_a2:
  classification of nonnegative real functions whose interval average equals
  the geometric mean of their endpoint values. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P62A2Sol F says that F is a total real function of the form
  a / (1 - c x)^2 with a nonnegative, taking the value zero where the
  denominator vanishes. P62A2P S F says that F is nonnegative on the reals
  and, for every positive x in S, its Lebesgue integral over [0,x], divided
  by x, is sqrt(F(0) F(x)).

  The closed integral interval is equivalent to the half-open interval in
  the Lean source because a singleton has Lebesgue measure zero.
  The final unproved assertion classifies both the positive half-line and
  arbitrary finite intervals with left endpoint zero. There are no $p proof
  statements in this database.
$)

$c P62A2Sol P62A2P $.

p62a2-solution-syntax $a wff ( P62A2Sol F ) $.
p62a2-property-syntax $a wff ( P62A2P S F ) $.

${
  $d a c x F $.
  $d c x $.

  p62a2-solution-definition $a |- (
    ( P62A2Sol F )
    <->
    (
      F : RR --> RR
      /\
      E. a e. RR E. c e. RR
        (
          0 <_ a
          /\
          A. x e. RR
            (
              (
                ( 1 - ( c x. x ) ) = 0
                ->
                ( F ` x ) = 0
              )
              /\
              (
                ( 1 - ( c x. x ) ) =/= 0
                ->
                ( F ` x )
                =
                (
                  a
                  /
                  ( ( 1 - ( c x. x ) ) ^ 2 )
                )
              )
            )
        )
    )
  ) $.
$}

${
  $d t x F $.
  $d t x S $.
  $d x F $.
  $d x S $.

  p62a2-property-definition $a |- (
    ( P62A2P S F )
    <->
    (
      F : RR --> RR
      /\
      (
        A. x e. RR 0 <_ ( F ` x )
        /\
        A. x e. S
          (
            0 < x
            ->
            (
              (
                S. ( 0 [,] x ) ( F ` t ) _d t
              )
              /
              x
            )
            =
            (
              sqrt
              `
              ( ( F ` 0 ) x. ( F ` x ) )
            )
          )
      )
    )
  ) $.
$}

${
  $d e x F $.
  $d e x G $.
  $d x F G $.

  putnambench-putnam-1962-a2 $a |- (
    (
      A. F
        (
          (
            ( P62A2P { x e. RR | 0 < x } F )
            ->
            E. G
              (
                ( P62A2Sol G )
                /\
                A. x e. { x e. RR | 0 <_ x }
                  ( F ` x ) = ( G ` x )
              )
          )
          /\
          A. e e. RR
            (
              0 < e
              ->
              (
                ( P62A2P { x e. RR | ( 0 < x /\ x < e ) } F )
                ->
                E. G
                  (
                    ( P62A2Sol G )
                    /\
                    A. x e. { x e. RR | ( 0 <_ x /\ x < e ) }
                      ( F ` x ) = ( G ` x )
                  )
              )
            )
        )
      /\
      A. F
        (
          ( P62A2Sol F )
          ->
          (
            ( P62A2P { x e. RR | 0 < x } F )
            \/
            E. e e. RR
              (
                0 < e
                /\
                ( P62A2P { x e. RR | ( 0 < x /\ x < e ) } F )
              )
          )
        )
    )
  ) $.
$}
