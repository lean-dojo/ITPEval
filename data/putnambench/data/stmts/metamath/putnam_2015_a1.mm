$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_a1: equality of the two areas between the positive branch of
  the hyperbola xy = 1 and the chords from an area-maximizing intermediate
  point to two fixed endpoints. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P15A1R2 is the real coordinate plane and P15A1Hyperbola is the branch
  y = 1 / x with x > 0. P15A1Hull is the convex hull of three points,
  expressed by internally existential nonnegative barycentric weights, and
  P15A1Area is its planar Lebesgue measure through set.mm's
  finite-dimensional volume function voln.

  The line-function parameter L is the uncurried form of the source's
  PPline: it is an arbitrary map from ordered pairs of real-plane points to
  total real functions, subject to the same chord equation whenever the
  first coordinates differ. The open-interval S. binders are the real
  Lebesgue integrals in the source conclusion.

  The final declaration is the single unproved $a corpus statement. It
  preserves the arbitrary hyperbola set, points, line function, universal
  area-maximality condition, and integral equality; this database contains
  no $p proof declaration.
$)

$c P15A1I P15A1R2 P15A1Hyperbola P15A1Hull P15A1Area $.

p15a1-index-syntax $a class P15A1I $.
p15a1-plane-syntax $a class P15A1R2 $.
p15a1-hyperbola-syntax $a class P15A1Hyperbola $.
p15a1-hull-syntax $a class ( P15A1Hull A B C ) $.
p15a1-area-syntax $a class ( P15A1Area A B C ) $.

p15a1-index-definition $a |- P15A1I = ( 1 ... 2 ) $.

p15a1-plane-definition $a |- P15A1R2 = ( RR ^m P15A1I ) $.

p15a1-hyperbola-definition $a |- P15A1Hyperbola = {
  q e. P15A1R2 |
  (
    ( q ` 2 ) = ( 1 / ( q ` 1 ) )
    /\
    0 < ( q ` 1 )
  )
} $.

${
  $d A B C j u v w z $.

  p15a1-hull-definition $a |- (
    P15A1Hull A B C
  ) = {
    z e. P15A1R2 |
    E. u e. RR E. v e. RR E. w e. RR
      (
        (
          0 <_ u
          /\
          (
            0 <_ v
            /\
            0 <_ w
          )
        )
        /\
        (
          ( ( u + v ) + w ) = 1
          /\
          z =
            (
              j e. P15A1I |->
                (
                  (
                    ( u x. ( A ` j ) )
                    +
                    ( v x. ( B ` j ) )
                  )
                  +
                  ( w x. ( C ` j ) )
                )
            )
        )
      )
  } $.
$}

p15a1-area-definition $a |- (
  P15A1Area A B C
) = (
  ( voln ` P15A1I )
  `
  ( P15A1Hull A B C )
) $.

${
  $d A B H L P Q X Y x $.

  putnambench-putnam-2015-a1 $a |-
    A. H e. ~P P15A1R2
      A. L e.
        (
          ( RR ^m RR )
          ^m
          ( P15A1R2 X. P15A1R2 )
        )
        A. A e. P15A1R2
          A. B e. P15A1R2
            A. P e. P15A1R2
              (
                (
                  (
                    H = P15A1Hyperbola
                    /\
                    (
                      (
                        A e. H
                        /\
                        (
                          B e. H
                          /\
                          ( A ` 1 ) < ( B ` 1 )
                        )
                      )
                      /\
                      (
                        (
                          P e. H
                          /\
                          (
                            ( A ` 1 ) < ( P ` 1 )
                            /\
                            ( P ` 1 ) < ( B ` 1 )
                          )
                        )
                        /\
                        A. Q e. P15A1R2
                          (
                            (
                              Q e. H
                              /\
                              (
                                ( A ` 1 ) < ( Q ` 1 )
                                /\
                                ( Q ` 1 ) < ( B ` 1 )
                              )
                            )
                            ->
                            (
                              ( P15A1Area A Q B )
                              <_
                              ( P15A1Area A P B )
                            )
                          )
                      )
                    )
                  )
                  /\
                  A. X e. P15A1R2 A. Y e. P15A1R2
                    (
                      ( X ` 1 ) =/= ( Y ` 1 )
                      ->
                      (
                        L ` <. X , Y >.
                      )
                      =
                      (
                        x e. RR |->
                          (
                            (
                              (
                                ( ( Y ` 2 ) - ( X ` 2 ) )
                                /
                                ( ( Y ` 1 ) - ( X ` 1 ) )
                              )
                              x.
                              ( x - ( X ` 1 ) )
                            )
                            +
                            ( X ` 2 )
                          )
                      )
                    )
                )
                ->
                (
                  S. ( ( A ` 1 ) (,) ( P ` 1 ) )
                    (
                      (
                        ( L ` <. A , P >. )
                        ` x
                      )
                      -
                      ( 1 / x )
                    )
                    _d x
                  =
                  S. ( ( P ` 1 ) (,) ( B ` 1 ) )
                    (
                      (
                        ( L ` <. P , B >. )
                        ` x
                      )
                      -
                      ( 1 / x )
                    )
                    _d x
                )
              )
  $.
$}
