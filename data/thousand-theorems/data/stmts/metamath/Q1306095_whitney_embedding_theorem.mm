$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1306095
  (thousand-theorems__metamath__Q1306095), "Whitney embedding theorem":
  every compact Hausdorff smooth finite-dimensional real manifold modeled
  with corners on a convex coordinate range with nonempty interior admits a
  smooth closed embedding into some finite-dimensional Euclidean space whose
  manifold derivative is injective everywhere. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Finite-dimensional real normed model spaces are normalized by a linear
  coordinate equivalence to Q1306095Vec d, the real functions on 1 ... d.
  Q1306095Eucl d and Q1306095Norm d are its Euclidean topology and norm.

  Q1306095HasFDerivWithin gives the epsilon-delta definition of a Frechet
  derivative using only points of the subset S. A linear map is represented
  by its d columns in R^m. Q1306095Model is the coordinate-normalized range
  of the source's real ModelWithCorners: a convex subset of the model vector
  space with nonempty Euclidean interior. The source model map and its
  continuous total inverse identify the arbitrary model type homeomorphically
  with this range, so transporting charts to the range is bidirectionally
  equivalent rather than a restriction. These conditions give the unique
  differentiability used by manifold derivatives.

  Q1306095JetWithin is the finite-coordinate form of ContDiffWithin infinity:
  it records all iterated within-set Frechet derivatives and requires each
  derivative field to be continuous in the subspace topology. This is an
  intrinsic definition on the model range and never asks for a smooth
  extension to the ambient space.

  An atlas consists of genuine homeomorphisms from open subsets of the
  arbitrary carrier topology to relatively open subsets of the model range,
  covers the carrier, and has intrinsically smooth transition maps. The
  conclusion keeps the Euclidean dimension and embedding internally
  existential. Q1306095ClosedEmbedding is a homeomorphism onto a closed
  image. Q1306095Immersion requires the unique first within-set derivative of
  each chart-coordinate representative to be injective on the full model
  vector space, exactly expressing injectivity of mfderiv.

  Every declaration before the final one is syntax or a bidirectional
  definition. The final $a declaration is the single unproved corpus
  statement. This database contains no $p proof statement.
$)

$c Q1306095Vec Q1306095Eucl Q1306095Norm Q1306095Diff
   Q1306095LinApply Q1306095One Q1306095Snoc Q1306095Deriv
   Q1306095HasFDerivWithin Q1306095JetWithin Q1306095CInfWithin
   Q1306095Model Q1306095Dom Q1306095Img Q1306095Map Q1306095Chart
   Q1306095Overlap Q1306095Transition Q1306095Manifold
   Q1306095SmoothMap Q1306095Jac Q1306095ClosedEmbedding
   Q1306095Immersion $.

q1306095-vec-syntax $a class ( Q1306095Vec d ) $.
q1306095-eucl-syntax $a class ( Q1306095Eucl d ) $.
q1306095-norm-syntax $a class ( Q1306095Norm d x ) $.
q1306095-diff-syntax $a class ( Q1306095Diff d x y ) $.
q1306095-lin-apply-syntax
  $a class ( Q1306095LinApply d m L v ) $.
q1306095-one-syntax $a class ( Q1306095One i ) $.
q1306095-snoc-syntax $a class ( Q1306095Snoc q r i ) $.
q1306095-deriv-syntax
  $a class ( Q1306095Deriv d D r q x ) $.
q1306095-has-fderiv-within-syntax
  $a wff ( Q1306095HasFDerivWithin d m S F x L ) $.
q1306095-jet-within-syntax
  $a wff ( Q1306095JetWithin d m S F D ) $.
q1306095-cinf-within-syntax
  $a wff ( Q1306095CInfWithin d m S F ) $.
q1306095-model-syntax $a wff ( Q1306095Model d H ) $.
q1306095-dom-syntax $a class ( Q1306095Dom c ) $.
q1306095-img-syntax $a class ( Q1306095Img c ) $.
q1306095-map-syntax $a class ( Q1306095Map c ) $.
q1306095-chart-syntax $a wff ( Q1306095Chart d H J c ) $.
q1306095-overlap-syntax $a class ( Q1306095Overlap c k ) $.
q1306095-transition-syntax $a class ( Q1306095Transition c k ) $.
q1306095-manifold-syntax $a wff ( Q1306095Manifold X J d H A ) $.
q1306095-smooth-map-syntax $a wff ( Q1306095SmoothMap X d n A e ) $.
q1306095-jac-syntax $a class ( Q1306095Jac d n D y v ) $.
q1306095-closed-embedding-syntax
  $a wff ( Q1306095ClosedEmbedding n J e ) $.
q1306095-immersion-syntax $a wff ( Q1306095Immersion d n A e ) $.

q1306095-vec-definition $a |-
  ( Q1306095Vec d ) = ( RR ^m ( 1 ... d ) ) $.

q1306095-eucl-definition $a |-
  ( Q1306095Eucl d ) =
  (
    Xt_ `
    ( ( 1 ... d ) X. { ( topGen ` ran (,) ) } )
  ) $.

${
  $d d i x $.

  q1306095-norm-definition $a |-
    ( Q1306095Norm d x ) =
    (
      sqrt `
      (
        sum_ i e. ( 1 ... d )
          ( ( x ` i ) ^ 2 )
      )
    ) $.
$}

${
  $d d i x y $.

  q1306095-diff-definition $a |-
    ( Q1306095Diff d x y ) =
    (
      i e. ( 1 ... d ) |->
      ( ( x ` i ) - ( y ` i ) )
    ) $.
$}

${
  $d L d i j m v $.

  q1306095-lin-apply-definition $a |-
    ( Q1306095LinApply d m L v ) =
    (
      j e. ( 1 ... m ) |->
      sum_ i e. ( 1 ... d )
        (
          ( ( ( L ` i ) ` j ) )
          x.
          ( v ` i )
        )
    ) $.
$}

${
  $d k i $.

  q1306095-one-definition $a |-
    ( Q1306095One i ) =
    ( k e. { 1 } |-> i ) $.
$}

${
  $d k i q r $.

  q1306095-snoc-definition $a |-
    ( Q1306095Snoc q r i ) =
    (
      k e. ( 1 ... ( r + 1 ) ) |->
      if ( k = ( r + 1 ) , i , ( q ` k ) )
    ) $.
$}

${
  $d D d i q r x $.

  q1306095-deriv-definition $a |-
    ( Q1306095Deriv d D r q x ) =
    (
      i e. ( 1 ... d ) |->
      (
        (
          D `
          <.
            ( r + 1 ) ,
            ( Q1306095Snoc q r i )
          >.
        )
        ` x
      )
    ) $.
$}

${
  $d F L S d i j m t u x y $.

  q1306095-has-fderiv-within-definition $a |- (
    ( Q1306095HasFDerivWithin d m S F x L )
    <->
    (
      (
        S C_ ( Q1306095Vec d )
        /\
        (
          F : S --> ( Q1306095Vec m )
          /\
          (
            x e. S
            /\
            L : ( 1 ... d ) --> ( Q1306095Vec m )
          )
        )
      )
      /\
      A. u e. RR+
        E. t e. RR+
          A. y e. S
            (
              (
                ( Q1306095Norm d
                    ( Q1306095Diff d y x ) )
                <
                t
              )
              ->
              (
                ( Q1306095Norm m
                    (
                      Q1306095Diff m
                        ( F ` y )
                        (
                          j e. ( 1 ... m ) |->
                          (
                            ( ( F ` x ) ` j )
                            +
                            (
                              (
                                Q1306095LinApply d m L
                                  ( Q1306095Diff d y x )
                              )
                              ` j
                            )
                          )
                        )
                    ) )
                <_
                (
                  u
                  x.
                  ( Q1306095Norm d
                      ( Q1306095Diff d y x ) )
                )
              )
            )
    )
  ) $.
$}

${
  $d D F S d m q r x $.

  q1306095-jet-within-definition $a |- (
    ( Q1306095JetWithin d m S F D )
    <->
    (
      (
        S C_ ( Q1306095Vec d )
        /\
        F : S --> ( Q1306095Vec m )
      )
      /\
      (
        A. r e. NN0
          A. q e. ( ( 1 ... d ) ^m ( 1 ... r ) )
            ( D ` <. r , q >. )
            e.
            (
              ( ( Q1306095Eucl d ) |`t S )
              Cn
              ( Q1306095Eucl m )
            )
        /\
        (
          A. q e. ( ( 1 ... d ) ^m ( 1 ... 0 ) )
            ( D ` <. 0 , q >. ) = F
          /\
          A. r e. NN0
            A. q e. ( ( 1 ... d ) ^m ( 1 ... r ) )
              A. x e. S
                (
                  Q1306095HasFDerivWithin d m S
                    ( D ` <. r , q >. )
                    x
                    ( Q1306095Deriv d D r q x )
                )
        )
      )
    )
  ) $.
$}

${
  $d D F S d m $.

  q1306095-cinf-within-definition $a |- (
    ( Q1306095CInfWithin d m S F )
    <->
    E. D
      ( Q1306095JetWithin d m S F D )
  ) $.
$}

${
  $d H d k t x y $.

  q1306095-model-definition $a |- (
    ( Q1306095Model d H )
    <->
    (
      (
        d e. NN0
        /\
        H C_ ( Q1306095Vec d )
      )
      /\
      (
        (
          ( ( int ` ( Q1306095Eucl d ) ) ` H )
          =/=
          (/)
        )
        /\
        A. x e. H
          A. y e. H
            A. t e. ( 0 [,] 1 )
              (
                k e. ( 1 ... d ) |->
                (
                  (
                    ( 1 - t )
                    x.
                    ( x ` k )
                  )
                  +
                  (
                    t
                    x.
                    ( y ` k )
                  )
                )
              )
              e. H
      )
    )
  ) $.
$}

q1306095-dom-definition $a |-
  ( Q1306095Dom c ) = ( c ` 0 ) $.

q1306095-img-definition $a |-
  ( Q1306095Img c ) = ( c ` 1 ) $.

q1306095-map-definition $a |-
  ( Q1306095Map c ) = ( c ` 2 ) $.

q1306095-chart-definition $a |- (
  ( Q1306095Chart d H J c )
  <->
  (
    c Fn ( 0 ..^ 3 )
    /\
    (
      ( Q1306095Dom c ) e. J
      /\
      (
        ( Q1306095Img c )
        e.
        (
          ( Q1306095Eucl d )
          |`t H
        )
      )
    )
    /\
    (
      ( Q1306095Map c )
      e.
      (
        ( J |`t ( Q1306095Dom c ) )
        Homeo
        (
          ( Q1306095Eucl d )
          |`t
          ( Q1306095Img c )
        )
      )
    )
  )
) $.

q1306095-overlap-definition $a |-
  ( Q1306095Overlap c k ) =
  (
    ( Q1306095Map c )
    "
    (
      ( Q1306095Dom c )
      i^i
      ( Q1306095Dom k )
    )
  ) $.

q1306095-transition-definition $a |-
  ( Q1306095Transition c k ) =
  (
    (
      ( Q1306095Map k )
      o.
      `' ( Q1306095Map c )
    )
    |`
    ( Q1306095Overlap c k )
  ) $.

${
  $d A H J X c d k x $.

  q1306095-manifold-definition $a |- (
    ( Q1306095Manifold X J d H A )
    <->
    (
      (
        J e. ( TopOn ` X )
        /\
        ( Q1306095Model d H )
      )
      /\
      (
        A. c e. A
          ( Q1306095Chart d H J c )
        /\
        A. x e. X
          E. c e. A
            x e. ( Q1306095Dom c )
      )
      /\
      A. c e. A
        A. k e. A
          (
            Q1306095CInfWithin d d
              ( Q1306095Overlap c k )
              ( Q1306095Transition c k )
          )
    )
  ) $.
$}

${
  $d A X c d e n $.

  q1306095-smooth-map-definition $a |- (
    ( Q1306095SmoothMap X d n A e )
    <->
    (
      e : X --> ( Q1306095Vec n )
      /\
      A. c e. A
        (
          Q1306095CInfWithin d n
            ( Q1306095Img c )
            (
              (
                e
                o.
                `' ( Q1306095Map c )
              )
              |`
              ( Q1306095Img c )
            )
        )
    )
  ) $.
$}

${
  $d D d i j n v y $.

  q1306095-jac-definition $a |-
    ( Q1306095Jac d n D y v ) =
    (
      j e. ( 1 ... n ) |->
      sum_ i e. ( 1 ... d )
        (
          (
            (
              (
                ( D ` <. 1 , ( Q1306095One i ) >. )
                ` y
              )
              ` j
            )
            x.
            ( v ` i )
          )
        )
    ) $.
$}

q1306095-closed-embedding-definition $a |- (
  ( Q1306095ClosedEmbedding n J e )
  <->
  (
    e
    e.
    (
      J
      Homeo
      (
        ( Q1306095Eucl n )
        |`t
        ran e
      )
    )
    /\
    ran e e. ( Clsd ` ( Q1306095Eucl n ) )
  )
) $.

${
  $d A D c d e n v w x $.

  q1306095-immersion-definition $a |- (
    ( Q1306095Immersion d n A e )
    <->
    A. c e. A
      A. x e. ( Q1306095Dom c )
        A. D
          (
            (
              Q1306095JetWithin d n
                ( Q1306095Img c )
                (
                  (
                    e
                    o.
                    `' ( Q1306095Map c )
                  )
                  |`
                  ( Q1306095Img c )
                )
                D
            )
            ->
            A. v e. ( Q1306095Vec d )
              A. w e. ( Q1306095Vec d )
                (
                  (
                    ( Q1306095Jac d n D
                        ( ( Q1306095Map c ) ` x ) v )
                    =
                    ( Q1306095Jac d n D
                        ( ( Q1306095Map c ) ` x ) w )
                  )
                  ->
                  v = w
                )
          )
  ) $.
$}

${
  $d A H J X d e n $.

  thousand-theorems-q1306095-whitney-embedding $a |-
    A. X A. J A. d A. H A. A
      (
        (
          ( Q1306095Manifold X J d H A )
          /\
          (
            J e. Haus
            /\
            J e. Comp
          )
        )
        ->
        E. n e. NN0
          E. e
            (
              ( Q1306095SmoothMap X d n A e )
              /\
              (
                ( Q1306095ClosedEmbedding n J e )
                /\
                ( Q1306095Immersion d n A e )
              )
            )
      )
  $.
$}
