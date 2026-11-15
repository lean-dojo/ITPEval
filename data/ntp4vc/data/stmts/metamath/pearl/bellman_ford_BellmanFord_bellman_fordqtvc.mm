$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bellman_ford_BellmanFord_bellman_fordqtvc: the Bellman-Ford
  verification condition states the initialization, edge-relaxation loop
  invariants, negative-cycle branch, and final shortest-path distance
  specification for a finite directed graph with integer weights. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source vertex, set-wrapper, and distance-map types are the
  nonempty SetMM carriers V, S, and D. G and E are respectively the finite
  vertex and directed-edge sets, W is the full integer weight function, T is
  to_fset, and H is choose1. SetMM words over V are exactly arbitrary finite
  zero-based source lists.

  NTP4VCIntInf is a disjoint tagged encoding of every source extended integer:
  <. n , 0 >. is Finite n and <. 0 , 1 >. is Infinite. Its addition and strict
  and non-strict orders expand the source definitions exactly.
  NTP4VCPath is equivalent in both directions to the source inductive path:
  the empty word connects a vertex to itself, while a nonempty word records
  the initial vertex and every edge before the final destination.
  NTP4VCPathWeight is the corresponding finite sum of consecutive edge
  weights and the last edge to the destination.

  C, R, Q, and U are contents, lookup, create, and update specialized to the
  only value type used by this VC, NTP4VCIntInf. Their source specifications
  are retained pointwise. NTP4VCInv1, NTP4VCInv2, NTP4VCPost,
  NTP4VCScan1, and NTP4VCScan2 are direct definitional expansions of the two
  invariants and nested loop/postcondition obligations. Each proposition-valued
  source if is rendered by its equivalent pair of guarded cases, and every
  let-bound value is substituted definitionally.

  All vertex, integer, finite-set, list, set-wrapper, and distance-map
  quantifiers retain their full source domains. The unused polymorphic
  instances and unused distmap carrier are conservatively extendible and do
  not alter this instantiated proposition. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCFinite NTP4VCInfinity NTP4VCIntInf
  NTP4VCInfAdd NTP4VCInfLt NTP4VCInfLe
  NTP4VCPath NTP4VCPathWeight NTP4VCNegativeCycle
  NTP4VCInv1 NTP4VCInv2 NTP4VCPost
  NTP4VCScan1 NTP4VCScan2
$.

ntp4vc-finite-syntax $a class ( NTP4VCFinite A ) $.
ntp4vc-infinity-syntax $a class NTP4VCInfinity $.
ntp4vc-intinf-syntax $a class NTP4VCIntInf $.
ntp4vc-inf-add-syntax $a class ( NTP4VCInfAdd A B ) $.
ntp4vc-inf-lt-syntax $a wff ( NTP4VCInfLt A B ) $.
ntp4vc-inf-le-syntax $a wff ( NTP4VCInfLe A B ) $.

ntp4vc-path-syntax
  $a wff ( NTP4VCPath A B C D E ) $.
ntp4vc-path-weight-syntax
  $a class ( NTP4VCPathWeight A B C ) $.
ntp4vc-negative-cycle-syntax
  $a wff ( NTP4VCNegativeCycle A B C D E F ) $.

ntp4vc-inv1-syntax
  $a wff ( NTP4VCInv1 A B C D E F G H I ) $.
ntp4vc-inv2-syntax
  $a wff ( NTP4VCInv2 A B C D E ) $.
ntp4vc-post-syntax
  $a wff ( NTP4VCPost A B C D E F G ) $.
ntp4vc-scan1-syntax
  $a wff ( NTP4VCScan1 A B C D E F G H I J K L ) $.
ntp4vc-scan2-syntax
  $a wff ( NTP4VCScan2 A B C D E F G H I J K L ) $.

ntp4vc-finite-def $a |- ( NTP4VCFinite A ) = <. A , 0 >. $.
ntp4vc-infinity-def $a |- NTP4VCInfinity = <. 0 , 1 >. $.
ntp4vc-intinf-def $a |- NTP4VCIntInf =
  ( ( ZZ X. { 0 } ) u. { NTP4VCInfinity } ) $.

ntp4vc-inf-add-def $a |- (
  NTP4VCInfAdd A B
) = if (
  ( ( 2nd ` A ) = 1 \/ ( 2nd ` B ) = 1 ) ,
  NTP4VCInfinity ,
  ( NTP4VCFinite ( ( 1st ` A ) + ( 1st ` B ) ) )
) $.

ntp4vc-inf-lt-def $a |- (
  NTP4VCInfLt A B
) <-> (
  (
    ( 2nd ` A ) = 0
    /\
    ( 2nd ` B ) = 1
  )
  \/
  (
    (
      ( 2nd ` A ) = 0
      /\
      ( 2nd ` B ) = 0
    )
    /\
    ( 1st ` A ) < ( 1st ` B )
  )
) $.

ntp4vc-inf-le-def $a |- (
  NTP4VCInfLe A B
) <-> (
  ( NTP4VCInfLt A B )
  \/
  A = B
) $.

${
  $d k A B C D E $.

  ntp4vc-path-def $a |- (
    NTP4VCPath A B C D E
  ) <-> (
    D e. Word A
    /\
    (
      (
        ( # ` D ) = 0
        /\
        C = E
      )
      \/
      (
        0 < ( # ` D )
        /\
        (
          ( D ` 0 ) = C
          /\
          (
            A. k e. ( 0 ..^ ( ( # ` D ) - 1 ) )
              <. ( D ` k ) , ( D ` ( k + 1 ) ) >. e. B
            /\
            <.
              ( D ` ( ( # ` D ) - 1 ) ) ,
              E
            >. e. B
          )
        )
      )
    )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-path-weight-def $a |- (
    NTP4VCPathWeight A B C
  ) = if (
    ( # ` B ) = 0 ,
    0 ,
    (
      sum_ k e. ( 0 ..^ ( ( # ` B ) - 1 ) )
        ( A ` <. ( B ` k ) , ( B ` ( k + 1 ) ) >. )
      +
      ( A ` <. ( B ` ( ( # ` B ) - 1 ) ) , C >. )
    )
  ) $.
$}

${
  $d l m A B C D E F $.

  ntp4vc-negative-cycle-def $a |- (
    NTP4VCNegativeCycle A B C D E F
  ) <-> (
    F e. B
    /\
    (
      E. l e. Word A
        ( NTP4VCPath A C D l F )
      /\
      E. m e. Word A
        (
          ( NTP4VCPath A C F m F )
          /\
          ( NTP4VCPathWeight E m F ) < 0
        )
    )
  ) $.
$}

${
  $d l n u v A B C D E F G H I $.

  ntp4vc-inv1-def $a |- (
    NTP4VCInv1 A B C D E F G H I
  ) <-> (
    A. v e. A
      (
        v e. B
        ->
        (
          E. n e. ZZ
            (
              ( F ` <. G , v >. ) = ( NTP4VCFinite n )
              /\
              (
                (
                  E. l e. Word A
                    (
                      ( NTP4VCPath A C D l v )
                      /\
                      ( NTP4VCPathWeight E l v ) = n
                    )
                  /\
                  A. l e. Word A
                    (
                      ( NTP4VCPath A C D l v )
                      ->
                      (
                        ( # ` l ) < H
                        ->
                        n <_ ( NTP4VCPathWeight E l v )
                      )
                    )
                )
                /\
                A. u e. A
                  A. l e. Word A
                    (
                      ( NTP4VCPath A C D l u )
                      ->
                      (
                        ( # ` l ) < H
                        ->
                        (
                          <. u , v >. e. I
                          ->
                          n <_
                            (
                              ( NTP4VCPathWeight E l u )
                              +
                              ( E ` <. u , v >. )
                            )
                        )
                      )
                    )
              )
            )
          \/
          (
            ( F ` <. G , v >. ) = NTP4VCInfinity
            /\
            (
              A. l e. Word A
                (
                  ( NTP4VCPath A C D l v )
                  ->
                  H <_ ( # ` l )
                )
              /\
              A. u e. A
                (
                  <. u , v >. e. I
                  ->
                  A. l e. Word A
                    (
                      ( NTP4VCPath A C D l u )
                      ->
                      H <_ ( # ` l )
                    )
                )
            )
          )
        )
      )
  ) $.
$}

${
  $d u v A B C D E $.

  ntp4vc-inv2-def $a |- (
    NTP4VCInv2 A B C D E
  ) <-> (
    A. u e. A
      A. v e. A
        (
          <. u , v >. e. E
          ->
          (
            NTP4VCInfLe
              ( C ` <. D , v >. )
              (
                NTP4VCInfAdd
                  ( C ` <. D , u >. )
                  ( NTP4VCFinite ( B ` <. u , v >. ) )
              )
          )
        )
  ) $.
$}

${
  $d l n v A B C D E F G $.

  ntp4vc-post-def $a |- (
    NTP4VCPost A B C D E F G
  ) <-> (
    A. v e. A
      (
        v e. B
        ->
        (
          E. n e. ZZ
            (
              ( F ` <. G , v >. ) = ( NTP4VCFinite n )
              /\
              (
                E. l e. Word A
                  (
                    ( NTP4VCPath A C D l v )
                    /\
                    ( NTP4VCPathWeight E l v ) = n
                  )
                /\
                A. l e. Word A
                  (
                    ( NTP4VCPath A C D l v )
                    ->
                    n <_ ( NTP4VCPathWeight E l v )
                  )
              )
            )
          \/
          (
            ( F ` <. G , v >. ) = NTP4VCInfinity
            /\
            A. l e. Word A
              -. ( NTP4VCPath A C D l v )
          )
        )
      )
  ) $.
$}

${
  $d e f i m n u v A B C D E F G H I J K L $.

  ntp4vc-scan1-def $a |- (
    NTP4VCScan1 A B C D E F G H I J K L
  ) <-> (
    A. e e. A
      (
        ( B ` e ) = F
        ->
        (
          (
            ( B ` e ) C_ F
            /\
            (
              NTP4VCInv1
                D E F G H J K L ( F \ ( B ` e ) )
            )
          )
          /\
          A. f e. A
            A. m e. I
              (
                (
                  ( B ` f ) C_ F
                  /\
                  (
                    NTP4VCInv1
                      D E F G H J m L ( F \ ( B ` f ) )
                  )
                )
                ->
                (
                  (
                    ( B ` f ) =/= (/)
                    /\
                    (
                      ( B ` f ) =/= (/)
                      /\
                      A. n e. A
                        (
                          (
                            ( C ` f ) e. ( B ` f )
                            /\
                            ( B ` n ) = ( ( B ` f ) \ { ( C ` f ) } )
                          )
                          ->
                          (
                            (
                              (
                                1 <_ L
                                /\
                                (
                                  ( C ` f ) e. F
                                  /\
                                  -. ( C ` f ) e.
                                    ( F \ ( B ` f ) )
                                )
                              )
                              /\
                              (
                                NTP4VCInv1
                                  D E F G H J m L
                                  ( F \ ( B ` f ) )
                              )
                            )
                            /\
                            A. u e. I
                              (
                                (
                                  NTP4VCInv1
                                    D E F G H J u L
                                    (
                                      ( F \ ( B ` f ) )
                                      u. { ( C ` f ) }
                                    )
                                )
                                ->
                                (
                                  (
                                    0 <_ ( # ` ( B ` f ) )
                                    /\
                                    ( # ` ( B ` n ) ) <
                                      ( # ` ( B ` f ) )
                                  )
                                  /\
                                  (
                                    ( B ` n ) C_ F
                                    /\
                                    (
                                      NTP4VCInv1
                                        D E F G H J u L
                                        ( F \ ( B ` n ) )
                                    )
                                  )
                                )
                              )
                          )
                        )
                    )
                  )
                  \/
                  (
                    ( B ` f ) = (/)
                    /\
                    (
                      NTP4VCInv1
                        D E F G H J m ( L + 1 ) (/)
                    )
                  )
                )
              )
        )
      )
  ) $.
$}

${
  $d e f n u v A B C D E F G H I J K L $.

  ntp4vc-scan2-def $a |- (
    NTP4VCScan2 A B C D E F G H I J K L
  ) <-> (
    A. e e. A
      (
        ( B ` e ) = F
        ->
        (
          (
            ( B ` e ) C_ F
            /\
            (
              NTP4VCInv2
                D H J L ( F \ ( B ` e ) )
            )
          )
          /\
          A. f e. A
            (
              (
                ( B ` f ) C_ F
                /\
                (
                  NTP4VCInv2
                    D H J L ( F \ ( B ` f ) )
                )
              )
              ->
              (
                (
                  ( B ` f ) =/= (/)
                  /\
                  (
                    ( B ` f ) =/= (/)
                    /\
                    A. n e. A
                      (
                        (
                          ( C ` f ) e. ( B ` f )
                          /\
                          ( B ` n ) = ( ( B ` f ) \ { ( C ` f ) } )
                        )
                        ->
                        (
                          (
                            J ` <. L , ( 2nd ` ( C ` f ) ) >.
                          )
                          =
                          (
                            K ` <. L , ( 2nd ` ( C ` f ) ) >.
                          )
                          ->
                          (
                            (
                              J ` <. L , ( 1st ` ( C ` f ) ) >.
                            )
                            =
                            (
                              K ` <. L , ( 1st ` ( C ` f ) ) >.
                            )
                            ->
                            (
                              (
                                (
                                  NTP4VCInfLt
                                    (
                                      NTP4VCInfAdd
                                        (
                                          J ` <.
                                            L ,
                                            ( 1st ` ( C ` f ) )
                                          >.
                                        )
                                        (
                                          NTP4VCFinite
                                            (
                                              H ` <.
                                                ( 1st ` ( C ` f ) ) ,
                                                ( 2nd ` ( C ` f ) )
                                              >.
                                            )
                                        )
                                    )
                                    (
                                      J ` <.
                                        L ,
                                        ( 2nd ` ( C ` f ) )
                                      >.
                                    )
                                )
                                /\
                                E. v e. D
                                  (
                                    NTP4VCNegativeCycle
                                      D E F G H v
                                  )
                              )
                              \/
                              (
                                -.
                                (
                                  NTP4VCInfLt
                                    (
                                      NTP4VCInfAdd
                                        (
                                          J ` <.
                                            L ,
                                            ( 1st ` ( C ` f ) )
                                          >.
                                        )
                                        (
                                          NTP4VCFinite
                                            (
                                              H ` <.
                                                ( 1st ` ( C ` f ) ) ,
                                                ( 2nd ` ( C ` f ) )
                                              >.
                                            )
                                        )
                                    )
                                    (
                                      J ` <.
                                        L ,
                                        ( 2nd ` ( C ` f ) )
                                      >.
                                    )
                                )
                                /\
                                (
                                  (
                                    0 <_ ( # ` ( B ` f ) )
                                    /\
                                    ( # ` ( B ` n ) ) <
                                      ( # ` ( B ` f ) )
                                  )
                                  /\
                                  (
                                    ( B ` n ) C_ F
                                    /\
                                    (
                                      NTP4VCInv2
                                        D H J L ( F \ ( B ` n ) )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                  )
                )
                \/
                (
                  ( B ` f ) = (/)
                  /\
                  ( NTP4VCPost D E F G H J L )
                )
              )
            )
        )
      )
  ) $.
$}

${
  $d e k m v x A C D E G H I J K L M N P Q R S T U V W $.

  $( Source graph carriers and data. $)
  ntp4vc-vertex-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-vertices-subset $e |- G C_ V $.
  ntp4vc-vertices-finite $e |- G e. Fin $.
  ntp4vc-edges-subset $e |- E C_ ( V X. V ) $.
  ntp4vc-edges-finite $e |- E e. Fin $.
  ntp4vc-edge-endpoints $e |- A. e e. E
    (
      ( 1st ` e ) e. G
      /\
      ( 2nd ` e ) e. G
    ) $.
  ntp4vc-source-vertex $e |- A e. G $.
  ntp4vc-weight-function $e |- W e. ( ZZ ^m ( V X. V ) ) $.

  $( Source finite-set wrapper and choice operation. $)
  ntp4vc-set-carrier-nonempty $e |- S =/= (/) $.
  ntp4vc-to-fset-function
    $e |- T e. ( ( ~P ( V X. V ) ) ^m S ) $.
  ntp4vc-to-fset-finite $e |- A. x e. S ( T ` x ) e. Fin $.
  ntp4vc-choose-function $e |- H e. ( ( V X. V ) ^m S ) $.
  ntp4vc-choose-spec $e |- A. x e. S
    (
      ( T ` x ) =/= (/)
      ->
      ( H ` x ) e. ( T ` x )
    ) $.

  $( Source distance-map carrier and its exact operations at IntInf. $)
  ntp4vc-map-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-contents-function
    $e |- C e. ( NTP4VCIntInf ^m ( D X. V ) ) $.
  ntp4vc-lookup-function
    $e |- R e. ( NTP4VCIntInf ^m ( D X. V ) ) $.
  ntp4vc-create-function $e |- Q e. ( D ^m NTP4VCIntInf ) $.
  ntp4vc-update-function
    $e |- U e. ( D ^m ( D X. ( V X. NTP4VCIntInf ) ) ) $.

  ntp4vc-create-spec $e |- A. x e. NTP4VCIntInf A. v e. V
    (
      C ` <. ( Q ` x ) , v >.
    ) = x $.
  ntp4vc-lookup-spec $e |- A. m e. D A. v e. V
    (
      R ` <. m , v >.
    ) = (
      C ` <. m , v >.
    ) $.
  ntp4vc-update-spec $e |- A. m e. D A. k e. V
    A. x e. NTP4VCIntInf A. v e. V
      (
        C ` <. ( U ` <. m , <. k , x >. >. ) , v >.
      )
      =
      if (
        v = k ,
        x ,
        ( C ` <. m , v >. )
      ) $.

  ntp4vc-pearl-bellman-ford-vc $a |- (
    (
      1 <_ ( ( ( # ` G ) - 1 ) + 1 )
      ->
      (
        (
          NTP4VCInv1
            V G E A W R
            (
              U ` <.
                ( Q ` NTP4VCInfinity ) ,
                <. A , ( NTP4VCFinite 0 ) >.
              >.
            )
            1 (/)
        )
        /\
        A. m e. D
          (
            A. i e. ZZ
              (
                (
                  (
                    1 <_ i
                    /\
                    i <_ ( ( # ` G ) - 1 )
                  )
                  /\
                  ( NTP4VCInv1 V G E A W R m i (/) )
                )
                ->
                (
                  NTP4VCScan1
                    S T H V G E A W D R m i
                )
              )
            /\
            (
              (
                NTP4VCInv1
                  V G E A W R m
                  ( ( ( # ` G ) - 1 ) + 1 ) (/)
              )
              ->
              (
                NTP4VCScan2
                  S T H V G E A W D R C m
              )
            )
          )
      )
    )
    /\
    (
      ( ( ( # ` G ) - 1 ) + 1 ) < 1
      ->
      (
        NTP4VCScan2
          S T H V G E A W D R C
          (
            U ` <.
              ( Q ` NTP4VCInfinity ) ,
              <. A , ( NTP4VCFinite 0 ) >.
            >.
          )
      )
    )
  ) $.
$}
