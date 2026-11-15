$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bellman_ford_BellmanFord_relaxqtvc: the Bellman-Ford relaxation
  verification condition states that processing a previously unprocessed
  directed edge preserves the path-distance invariant, whether or not the
  destination distance is updated. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source vertex and distance-map types are the nonempty SetMM
  carriers V and D. G and E are respectively the finite vertex and directed
  edge sets, W is the full integer weight function, and A is the distinguished
  source vertex. SetMM words over V are exactly arbitrary finite zero-based
  source lists.

  NTP4VCIntInf is a disjoint tagged encoding of every source extended integer:
  <. n , 0 >. is Finite n and <. 0 , 1 >. is Infinite. NTP4VCInfAdd and
  NTP4VCInfLt expand the source definitions exactly. NTP4VCPath is equivalent
  in both directions to the source inductive path, and NTP4VCPathWeight is its
  corresponding finite integer weight sum.

  C, R, and U are contents, lookup, and update specialized to the only value
  type used by this verification condition, NTP4VCIntInf. Their source
  specifications are retained pointwise. NTP4VCInv1 directly expands the
  source invariant. The source let-bound values are substituted
  definitionally, and its proposition-valued if is represented by the
  equivalent pair of guarded cases.

  Every vertex, integer, finite edge set, list, and distance-map quantifier
  retains its full source domain. The unused set-wrapper, choice, create, and
  distmap declarations are conservatively extendible and do not alter this
  instantiated proposition. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCFinite NTP4VCInfinity NTP4VCIntInf
  NTP4VCInfAdd NTP4VCInfLt
  NTP4VCPath NTP4VCPathWeight NTP4VCInv1
$.

ntp4vc-finite-syntax $a class ( NTP4VCFinite A ) $.
ntp4vc-infinity-syntax $a class NTP4VCInfinity $.
ntp4vc-intinf-syntax $a class NTP4VCIntInf $.
ntp4vc-inf-add-syntax $a class ( NTP4VCInfAdd A B ) $.
ntp4vc-inf-lt-syntax $a wff ( NTP4VCInfLt A B ) $.
ntp4vc-path-syntax
  $a wff ( NTP4VCPath A B C D E ) $.
ntp4vc-path-weight-syntax
  $a class ( NTP4VCPathWeight A B C ) $.
ntp4vc-inv1-syntax
  $a wff ( NTP4VCInv1 A B C D E F G H I ) $.

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
  $d e f i k l m n u v x A C D E G R U V W $.

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

  $( Source distance-map carrier and its exact operations at IntInf. $)
  ntp4vc-map-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-contents-function
    $e |- C e. ( NTP4VCIntInf ^m ( D X. V ) ) $.
  ntp4vc-lookup-function
    $e |- R e. ( NTP4VCIntInf ^m ( D X. V ) ) $.
  ntp4vc-update-function
    $e |- U e. ( D ^m ( D X. ( V X. NTP4VCIntInf ) ) ) $.

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

  ntp4vc-pearl-bellman-ford-relax-vc $a |- A. i e. ZZ
    A. u e. V
      A. v e. V
        A. f e. ( ~P ( V X. V ) )
          A. m e. D
            (
              (
                f e. Fin
                /\
                (
                  1 <_ i
                  /\
                  (
                    <. u , v >. e. E
                    /\
                    (
                      -. <. u , v >. e. f
                      /\
                      ( NTP4VCInv1 V G E A W R m i f )
                    )
                  )
                )
              )
              ->
              (
                (
                  R ` <. m , u >.
                ) = (
                  C ` <. m , u >.
                )
                ->
                (
                  (
                    R ` <. m , v >.
                  ) = (
                    C ` <. m , v >.
                  )
                  ->
                  (
                    (
                      (
                        NTP4VCInfLt
                          (
                            NTP4VCInfAdd
                              ( R ` <. m , u >. )
                              (
                                NTP4VCFinite
                                  ( W ` <. u , v >. )
                              )
                          )
                          ( R ` <. m , v >. )
                      )
                      /\
                      (
                        NTP4VCInv1
                          V G E A W R
                          (
                            U ` <.
                              m ,
                              <.
                                v ,
                                (
                                  NTP4VCInfAdd
                                    ( R ` <. m , u >. )
                                    (
                                      NTP4VCFinite
                                        ( W ` <. u , v >. )
                                    )
                                )
                              >.
                            >.
                          )
                          i
                          ( f u. { <. u , v >. } )
                      )
                    )
                    \/
                    (
                      -.
                      (
                        NTP4VCInfLt
                          (
                            NTP4VCInfAdd
                              ( R ` <. m , u >. )
                              (
                                NTP4VCFinite
                                  ( W ` <. u , v >. )
                              )
                          )
                          ( R ` <. m , v >. )
                      )
                      /\
                      (
                        NTP4VCInv1
                          V G E A W R m i
                          ( f u. { <. u , v >. } )
                      )
                    )
                  )
                )
              )
            ) $.
$}
