$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/schorr_waite_via_recursion_SchorrWaite_schorr_waiteqtvc:
  the recursive Schorr-Waite graph-marking verification condition,
  including the body, recursive traversal, loop invariant, frame,
  termination, reachability, and final coloring obligations. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Locations range over the arbitrary nonempty set U and Z is null. Colors
  are represented by the disjoint tagged values 0 (White), 1 (Black none),
  and <. 2 , i >. (Black (some i)), for every integer i. A memory is exactly
  a product of a U-to-integer block-size function, a curried U-to-integer-
  to-U accessor, and a U-to-color function. Thus the source record and all
  quantified memories retain their full function spaces.

  The definitions below are direct set-theoretic expansions of the source
  predicates. NTP4VCPath is equivalent to the inductive reflexive transitive
  path relation by a finite-word witness. Propositional conditionals are
  represented by their two guarded branches. Every auxiliary $a is syntax
  or an explicit definition; the final $a is the native statement-only
  declaration. There is no $p declaration.
$)

$c
  NTP4VCColor NTP4VCMemory NTP4VCFSet
  NTP4VCBS NTP4VCAC NTP4VCCL NTP4VCUpdate NTP4VCAUpdate
  NTP4VCEdge NTP4VCPath NTP4VCColorValid NTP4VCWell
  NTP4VCUnchanged NTP4VCBodyPre NTP4VCPopSwing
  NTP4VCBodyNormal NTP4VCBodyRaises NTP4VCBlackBranch
  NTP4VCWhiteBranch NTP4VCBodyImpl NTP4VCUnmarked
  NTP4VCAuxPre NTP4VCPreserve NTP4VCStable NTP4VCAuxPost
  NTP4VCVariant NTP4VCLoopInv NTP4VCExplore NTP4VCLoopVC
  NTP4VCAuxImpl NTP4VCFinal NTP4VCMain NTP4VCStatement
$.

ntp4vc-color-syn $a class NTP4VCColor $.
ntp4vc-memory-syn $a class ( NTP4VCMemory A ) $.
ntp4vc-fset-syn $a class ( NTP4VCFSet A ) $.
ntp4vc-bs-syn $a class ( NTP4VCBS A ) $.
ntp4vc-ac-syn $a class ( NTP4VCAC A ) $.
ntp4vc-cl-syn $a class ( NTP4VCCL A ) $.
ntp4vc-update-syn $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-aupdate-syn $a class ( NTP4VCAUpdate A B C D E ) $.
ntp4vc-edge-syn $a wff ( NTP4VCEdge A B C D E ) $.
ntp4vc-path-syn $a wff ( NTP4VCPath A B C D E ) $.
ntp4vc-color-valid-syn $a wff ( NTP4VCColorValid A B ) $.
ntp4vc-well-syn $a wff ( NTP4VCWell A B C D E F ) $.
ntp4vc-unchanged-syn $a wff ( NTP4VCUnchanged A B C D ) $.
ntp4vc-body-pre-syn $a wff ( NTP4VCBodyPre A B C D ) $.
ntp4vc-pop-swing-syn
  $a wff ( NTP4VCPopSwing A B C D E F G ) $.
ntp4vc-body-normal-syn
  $a wff ( NTP4VCBodyNormal A B C D E F G H ) $.
ntp4vc-body-raises-syn
  $a wff ( NTP4VCBodyRaises A B C D E ) $.
ntp4vc-black-branch-syn
  $a wff ( NTP4VCBlackBranch A B C D E ) $.
ntp4vc-white-branch-syn
  $a wff ( NTP4VCWhiteBranch A B C D E ) $.
ntp4vc-body-impl-syn $a wff ( NTP4VCBodyImpl A B C ) $.
ntp4vc-unmarked-syn $a wff ( NTP4VCUnmarked A B C D ) $.
ntp4vc-aux-pre-syn $a wff ( NTP4VCAuxPre A B C D E F G ) $.
ntp4vc-preserve-syn
  $a wff ( NTP4VCPreserve A B C D E F ) $.
ntp4vc-stable-syn
  $a wff ( NTP4VCStable A B C D E F G H ) $.
ntp4vc-aux-post-syn
  $a wff ( NTP4VCAuxPost A B C D E F G H I J K ) $.
ntp4vc-variant-syn $a wff ( NTP4VCVariant A B C ) $.
ntp4vc-loop-inv-syn
  $a wff ( NTP4VCLoopInv A B C D E F G H I J K L M ) $.
ntp4vc-explore-syn
  $a wff ( NTP4VCExplore A B C D E F G H I J ) $.
ntp4vc-loop-vc-syn
  $a wff ( NTP4VCLoopVC A B C D E F G H I J K L M ) $.
ntp4vc-aux-impl-syn $a wff ( NTP4VCAuxImpl A B C D ) $.
ntp4vc-final-syn $a wff ( NTP4VCFinal A B C D E ) $.
ntp4vc-main-syn $a wff ( NTP4VCMain A B C D E ) $.
ntp4vc-statement-syn $a wff ( NTP4VCStatement A B ) $.

ntp4vc-color-def $a |- NTP4VCColor =
  ( { 0 , 1 } u. ( { 2 } X. ZZ ) ) $.

ntp4vc-memory-def $a |- ( NTP4VCMemory A ) =
  ( ( ZZ ^m A ) X.
    ( ( ( A ^m ZZ ) ^m A ) X. ( NTP4VCColor ^m A ) ) ) $.

${
  $d s A $.
  ntp4vc-fset-def $a |- ( NTP4VCFSet A ) =
    { s e. Fin | s C_ A } $.
$}

ntp4vc-bs-def $a |- ( NTP4VCBS A ) = ( 1st ` A ) $.
ntp4vc-ac-def $a |- ( NTP4VCAC A ) = ( 1st ` ( 2nd ` A ) ) $.
ntp4vc-cl-def $a |- ( NTP4VCCL A ) = ( 2nd ` ( 2nd ` A ) ) $.

${
  $d x A B C D $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C D ) =
    ( x e. D |-> if ( x = B , C , ( A ` x ) ) ) $.
$}

ntp4vc-aupdate-def $a |- ( NTP4VCAUpdate A B C D E ) =
  ( NTP4VCUpdate A B
    ( NTP4VCUpdate ( A ` B ) C D ZZ ) E ) $.

${
  $d i A B C D E $.
  ntp4vc-edge-def $a |- ( NTP4VCEdge A B C D E ) <-> (
    C =/= B /\
    E. i e. ZZ (
      ( 0 <_ i /\ i < ( ( NTP4VCBS A ) ` C ) ) /\
      ( ( ( NTP4VCAC A ) ` C ) ` i ) = D
    )
  ) $.
$}

${
  $d h k A B C D E $.
  ntp4vc-path-def $a |- ( NTP4VCPath A B C D E ) <-> (
    E. h e. Word A (
      ( ( # ` h ) = 0 /\ D = E ) \/
      ( 0 < ( # ` h ) /\
        ( ( h ` 0 ) = D /\
          ( A. k e. ( 0 ..^ ( ( # ` h ) - 1 ) )
              ( NTP4VCEdge C B ( h ` k ) ( h ` ( k + 1 ) ) A ) /\
            ( NTP4VCEdge C B ( h ` ( ( # ` h ) - 1 ) ) E A ) ) )
    )
  ) $.
$}

${
  $d i A B $.
  ntp4vc-color-valid-def $a |- ( NTP4VCColorValid A B ) <-> (
    E. i e. ZZ (
      ( ( NTP4VCCL A ) ` B ) = <. 2 , i >. /\
      ( 0 <_ i /\ i < ( ( NTP4VCBS A ) ` B ) )
    )
  ) $.
$}

${
  $d x y A B C D E F $.
  ntp4vc-well-def $a |- ( NTP4VCWell A B C D E F ) <-> (
    B C_ A /\
    ( A. x e. E A. y e. E (
      ( ( ( x e. A /\ ( NTP4VCEdge C D x y E ) ) /\
          y =/= D ) /\ ( F ` x ) =/= 0 )
      -> ( x e. B \/ ( F ` y ) =/= 0 )
    ) /\
    A. x e. E ( x e. B -> ( F ` x ) =/= 0 ) )
  ) $.
$}

${
  $d i x A B C D $.
  ntp4vc-unchanged-def $a |- ( NTP4VCUnchanged A B C D ) <-> (
    A. x e. A A. i e. ZZ (
      ( ( x =/= B /\ 0 <_ i ) /\ i < ( ( NTP4VCBS C ) ` x ) )
      -> ( ( ( NTP4VCAC D ) ` x ) ` i )
         = ( ( ( NTP4VCAC C ) ` x ) ` i )
    )
  ) $.
$}

ntp4vc-body-pre-def $a |- ( NTP4VCBodyPre A B C D ) <-> (
  ( ( C =/= B /\ ( D = B \/ ( ( NTP4VCCL A ) ` D ) =/= 0 ) )
    -> ( NTP4VCColorValid A C ) )
) $.

${
  $d i A B C D E F G $.
  ntp4vc-pop-swing-def $a |-
    ( NTP4VCPopSwing A B C D E F G ) <-> (
      E. i e. ZZ (
        ( ( NTP4VCCL C ) ` D ) = <. 2 , i >. /\
        (
          ( ( i + 1 ) = ( ( NTP4VCBS C ) ` D ) ->
            ( G = D /\ ( F = ( ( ( NTP4VCAC C ) ` D ) ` i ) /\
              ( NTP4VCCL E ) = ( NTP4VCCL C ) /\
              ( NTP4VCAC E ) =
                ( NTP4VCAUpdate ( NTP4VCAC C ) D i A B ) ) ) )
          /\
          ( ( i + 1 ) =/= ( ( NTP4VCBS C ) ` D ) ->
            ( F = D /\
              ( G = ( ( ( NTP4VCAC C ) ` D ) ` ( i + 1 ) ) /\
                ( NTP4VCCL E ) =
                  ( NTP4VCUpdate ( NTP4VCCL C ) D <. 2 , ( i + 1 ) >. B ) /\
                ( NTP4VCAC E ) =
                  ( NTP4VCAUpdate
                    ( NTP4VCAUpdate ( NTP4VCAC C ) D ( i + 1 )
                      ( ( ( NTP4VCAC C ) ` D ) ` i ) B )
                    D i A B ) ) ) )
        )
      )
    ) $.
$}

ntp4vc-body-normal-def $a |-
  ( NTP4VCBodyNormal A B C D E F G H ) <-> (
    ( D =/= B \/ ( E =/= B /\ ( ( NTP4VCCL C ) ` E ) = 0 ) ) /\
    ( ( ( E =/= B /\ ( ( NTP4VCCL C ) ` E ) = 0 ) /\
          ( ( NTP4VCBS C ) ` E ) = 0 )
      -> ( ( NTP4VCCL F ) =
             ( NTP4VCUpdate ( NTP4VCCL C ) E 1 A ) /\
           ( H = E /\ ( G = D /\ ( NTP4VCAC F ) = ( NTP4VCAC C ) ) ) ) ) /\
    ( ( ( E =/= B /\ ( ( NTP4VCCL C ) ` E ) = 0 ) /\
          0 < ( ( NTP4VCBS C ) ` E ) )
      -> ( ( NTP4VCCL F ) =
             ( NTP4VCUpdate ( NTP4VCCL C ) E <. 2 , 0 >. A ) /\
           ( H = ( ( ( NTP4VCAC C ) ` E ) ` 0 ) /\
             ( G = E /\ ( NTP4VCAC F ) =
               ( NTP4VCAUpdate ( NTP4VCAC C ) E 0 D A ) ) ) ) ) /\
    ( ( E = B \/ ( ( NTP4VCCL C ) ` E ) =/= 0 )
      -> ( NTP4VCPopSwing E A C D F G H ) )
  ) $.

ntp4vc-body-raises-def $a |-
  ( NTP4VCBodyRaises A B C D E ) <-> (
    ( C = B /\ ( D = B \/ ( ( NTP4VCCL A ) ` D ) =/= 0 ) ) /\
    ( ( NTP4VCCL E ) = ( NTP4VCCL A ) /\
      ( NTP4VCAC E ) = ( NTP4VCAC A ) )
  ) $.

${
  $d i m n x A B C D E $.
  ntp4vc-black-branch-def $a |-
    ( NTP4VCBlackBranch A B C D E ) <-> (
      C =/= B /\
      E. i e. ZZ (
        ( ( NTP4VCCL A ) ` C ) = <. 2 , i >. /\
        ( C =/= B /\
          ( 0 <_ ( ( NTP4VCBS A ) ` C ) ->
            ( ( ( i + 1 ) = ( ( NTP4VCBS A ) ` C ) ->
                ( ( C =/= B /\ ( 0 <_ i /\
                    i < ( ( NTP4VCBS A ) ` C ) ) ) /\
                  A. n e. ( NTP4VCMemory E ) (
                    ( ( NTP4VCBS n ) = ( NTP4VCBS A ) /\
                      ( NTP4VCCL n ) = ( NTP4VCCL A ) )
                    -> ( ( NTP4VCAC n ) =
                         ( NTP4VCAUpdate ( NTP4VCAC A ) C i D E )
                      -> ( NTP4VCBodyNormal E B A C D n
                           ( ( ( NTP4VCAC A ) ` C ) ` i ) C ) )
                  ) ) ) /\
              ( ( i + 1 ) =/= ( ( NTP4VCBS A ) ` C ) ->
                ( ( C =/= B /\ ( 0 <_ ( i + 1 ) /\
                    ( i + 1 ) < ( ( NTP4VCBS A ) ` C ) ) ) /\
                  A. m e. ( NTP4VCMemory E ) (
                    ( ( NTP4VCBS m ) = ( NTP4VCBS A ) /\
                      ( NTP4VCCL m ) = ( NTP4VCCL A ) )
                    -> ( ( NTP4VCAC m ) =
                         ( NTP4VCAUpdate ( NTP4VCAC A ) C ( i + 1 )
                           ( ( ( NTP4VCAC A ) ` C ) ` i ) E )
                      -> ( ( C =/= B /\ ( 0 <_ i /\
                            i < ( ( NTP4VCBS m ) ` C ) ) ) /\
                        A. n e. ( NTP4VCMemory E ) (
                          ( ( NTP4VCBS n ) = ( NTP4VCBS m ) /\
                            ( NTP4VCCL n ) = ( NTP4VCCL m ) )
                          -> ( ( NTP4VCAC n ) =
                               ( NTP4VCAUpdate ( NTP4VCAC m ) C i D E )
                            -> A. x e. ( NTP4VCMemory E ) (
                              ( ( NTP4VCBS x ) = ( NTP4VCBS n ) /\
                                ( NTP4VCAC x ) = ( NTP4VCAC n ) )
                              -> ( ( NTP4VCCL x ) =
                                   ( NTP4VCUpdate ( NTP4VCCL n ) C
                                     <. 2 , ( i + 1 ) >. E )
                                -> ( NTP4VCBodyNormal E B A C D x C
                                  ( ( ( NTP4VCAC A ) ` C ) ` ( i + 1 ) ) ) )
                            ) )
                        ) ) )
                  ) ) ) )
          ) )
      )
    ) $.
$}

${
  $d m n A B C D E $.
  ntp4vc-white-branch-def $a |-
    ( NTP4VCWhiteBranch A B C D E ) <-> (
      D =/= B /\
      ( 0 <_ ( ( NTP4VCBS A ) ` D ) ->
        ( ( ( ( NTP4VCBS A ) ` D ) = 0 ->
              A. n e. ( NTP4VCMemory E ) (
                ( ( NTP4VCBS n ) = ( NTP4VCBS A ) /\
                  ( NTP4VCAC n ) = ( NTP4VCAC A ) )
                -> ( ( NTP4VCCL n ) =
                     ( NTP4VCUpdate ( NTP4VCCL A ) D 1 E )
                  -> ( NTP4VCBodyNormal E B A C D n C D ) )
              ) ) /\
            ( ( ( NTP4VCBS A ) ` D ) =/= 0 ->
              ( ( D =/= B /\ 0 < ( ( NTP4VCBS A ) ` D ) ) /\
                A. m e. ( NTP4VCMemory E ) (
                  ( ( NTP4VCBS m ) = ( NTP4VCBS A ) /\
                    ( NTP4VCCL m ) = ( NTP4VCCL A ) )
                  -> ( ( NTP4VCAC m ) =
                       ( NTP4VCAUpdate ( NTP4VCAC A ) D 0 C E )
                    -> ( ( D =/= B /\ 0 < ( ( NTP4VCBS m ) ` D ) ) /\
                      A. n e. ( NTP4VCMemory E ) (
                        ( ( NTP4VCBS n ) = ( NTP4VCBS m ) /\
                          ( NTP4VCAC n ) = ( NTP4VCAC m ) )
                        -> ( ( NTP4VCCL n ) =
                             ( NTP4VCUpdate ( NTP4VCCL m ) D <. 2 , 0 >. E )
                          -> ( NTP4VCBodyNormal E B A C D n D
                            ( ( ( NTP4VCAC A ) ` D ) ` 0 ) ) )
                      ) ) )
                ) ) ) )
        ) )
    ) $.
$}

${
  $d c d m o p t A B C $.
  ntp4vc-body-impl-def $a |- ( NTP4VCBodyImpl A B C ) <-> (
    A. p e. A A. t e. A A. m e. ( NTP4VCMemory A ) (
      ( NTP4VCBS m ) = ( NTP4VCBS C )
      -> ( ( NTP4VCBodyPre m B p t ) ->
        A. o e. { 0 , 1 } (
          o = if ( p = B ,
            if ( t = B , 1 , if ( ( ( NTP4VCCL m ) ` t ) =/= 0 , 1 , 0 ) ,
            0 )
          -> ( ( o = 1 ->
                ( p = B /\ ( t = B \/ ( ( NTP4VCCL m ) ` t ) =/= 0 ) ) )
            /\ ( o =/= 1 ->
              A. d e. { 0 , 1 } (
                d = if ( t = B , 1 ,
                  if ( ( ( NTP4VCCL m ) ` t ) =/= 0 , 1 , 0 )
                -> ( ( d = 1 -> ( NTP4VCBlackBranch m B p t A ) )
                  /\ ( d =/= 1 -> ( NTP4VCWhiteBranch m B p t A ) ) )
              ) ) )
        )
      ) )
    )
  ) $.
$}

${
  $d i x A B C D $.
  ntp4vc-unmarked-def $a |- ( NTP4VCUnmarked A B C D ) <-> (
    A. x e. A A. i e. ZZ (
      ( ( ( x =/= B /\ ( ( NTP4VCCL D ) ` x ) = 0 ) /\ 0 <_ i )
          /\ i < ( ( NTP4VCBS D ) ` x ) )
      -> ( ( ( NTP4VCAC D ) ` x ) ` i )
         = ( ( ( NTP4VCAC C ) ` x ) ` i )
    )
  ) $.
$}

ntp4vc-aux-pre-def $a |- ( NTP4VCAuxPre A B C D E F G ) <-> (
  ( NTP4VCWell B C D E A ( NTP4VCCL F ) ) /\
  ( G e. B /\ ( NTP4VCUnmarked A E D F ) )
) $.

${
  $d x A B C D E F $.
  ntp4vc-preserve-def $a |-
    ( NTP4VCPreserve A B C D E F ) <-> (
      A. x e. A (
        x =/= B ->
        ( ( -. ( NTP4VCPath A B C E x ) \/
            ( ( NTP4VCCL D ) ` x ) =/= 0 )
          -> ( ( NTP4VCCL F ) ` x ) = ( ( NTP4VCCL D ) ` x ) )
      )
    ) $.
$}

ntp4vc-stable-def $a |- ( NTP4VCStable A B C D E F G H ) <-> (
  ( NTP4VCUnchanged A B F H ) /\
  ( ( NTP4VCWell C D E B A ( NTP4VCCL H ) ) /\
    ( ( ( NTP4VCCL H ) ` G ) =/= 0 \/ G = B ) /\
    ( NTP4VCPreserve A B E F G H ) )
) $.

ntp4vc-aux-post-def $a |-
  ( NTP4VCAuxPost A B C D E F G H I J K ) <-> (
    ( K = H /\ J = G ) /\
    ( ( NTP4VCUnchanged A B F I ) /\
      ( ( NTP4VCWell C D E B A ( NTP4VCCL I ) ) /\
        ( ( ( NTP4VCCL I ) ` K ) =/= 0 \/ K = B ) /\
        ( NTP4VCPreserve A B E F K I ) ) )
  ) $.

ntp4vc-variant-def $a |- ( NTP4VCVariant A B C ) <-> (
  0 <_ ( ( # ` A ) - ( # ` B ) ) /\
  ( ( # ` A ) - ( # ` C ) ) < ( ( # ` A ) - ( # ` B ) )
) $.

${
  $d i x A B C D E F G H I J K L M $.
  ntp4vc-loop-inv-def $a |-
    ( NTP4VCLoopInv A B C D E F G H I J K L M ) <-> (
      ( NTP4VCWell A B C M L ( NTP4VCCL I ) ) /\
      ( J = F /\ ( K = ( ( ( NTP4VCAC C ) ` J ) ` H ) /\
        ( ( NTP4VCCL I ) ` J ) = <. 2 , H >. /\
        ( A. i e. ZZ (
            ( ( 0 <_ i /\ i < G ) /\ i =/= H )
            -> ( ( ( NTP4VCAC I ) ` J ) ` i )
               = ( ( ( NTP4VCAC D ) ` J ) ` i )
          ) /\
          ( ( ( NTP4VCAC I ) ` J ) ` H ) = E /\
          ( A. x e. L A. i e. ZZ (
              ( ( ( x =/= M /\ x =/= J ) /\ 0 <_ i ) /\
                  i < ( ( NTP4VCBS I ) ` x ) )
              -> ( ( ( NTP4VCAC I ) ` x ) ` i )
                 = ( ( ( NTP4VCAC D ) ` x ) ` i )
            ) /\
            ( A. i e. ZZ (
                ( 0 <_ i /\ i < H )
                -> ( ( ( ( NTP4VCAC I ) ` J ) ` i ) = M \/
                     ( ( NTP4VCCL I ) `
                       ( ( ( NTP4VCAC I ) ` J ) ` i ) ) =/= 0 )
              ) /\
              A. x e. L (
                x =/= M ->
                ( ( -. ( NTP4VCPath L M C J x ) \/
                    ( ( NTP4VCCL D ) ` x ) =/= 0 )
                  -> ( ( NTP4VCCL I ) ` x )
                     = ( ( NTP4VCCL D ) ` x ) )
              ) ) ) ) )
    ) $.
$}

${
  $d m p t x y A B C D E F G H I J $.
  ntp4vc-explore-def $a |-
    ( NTP4VCExplore A B C D E F G H I J ) <-> (
      ( NTP4VCVariant A B C /\
        ( NTP4VCAuxPre I A C D J E G ) ) /\
      A. m e. ( NTP4VCMemory I ) (
        ( NTP4VCBS m ) = ( NTP4VCBS E )
        -> ( ( NTP4VCStable I J A C D E G m )
          -> ( ( NTP4VCBodyPre m J F G ) /\
            A. p e. I A. t e. I A. x e. ( NTP4VCMemory I ) (
              ( NTP4VCBS x ) = ( NTP4VCBS m )
              -> ( ( NTP4VCBodyNormal I J m F G x p t )
                -> ( ( H ` <. x , <. p , t >. >. ) = 1 /\
                  -. ( NTP4VCBodyRaises m J F G x ) ) )
            )
          ) )
      )
    ) $.
$}

${
  $d c i m p t A B C D E F G H I J K L M $.
  ntp4vc-loop-vc-def $a |-
    ( NTP4VCLoopVC A B C D E F G H I J K L M ) <-> (
      ( 0 <_ ( H - 1 ) ->
        ( ( NTP4VCLoopInv A C D E F G H 0 I J K L M ) /\
          A. p e. L A. t e. L A. m e. ( NTP4VCMemory L )
          A. i e. ZZ (
            ( NTP4VCBS m ) = ( NTP4VCBS I )
            -> ( ( ( 0 <_ i /\ i <_ ( H - 2 ) ) /\
                    ( NTP4VCLoopInv A C D E F G H i m p t L M ) )
              -> ( NTP4VCExplore A B C D m p t
                ( c e. ( ( NTP4VCMemory L ) X. ( L X. L ) ) |->
                  if ( ( NTP4VCLoopInv A C D E F G H ( i + 1 )
                           ( 1st ` c ) ( 1st ` ( 2nd ` c ) )
                           ( 2nd ` ( 2nd ` c ) ) L M ) , 1 , 0 ) )
                L M ) )
          ) ) ) /\
      ( ( A. p e. L A. t e. L A. m e. ( NTP4VCMemory L ) (
            ( NTP4VCBS m ) = ( NTP4VCBS I )
            -> ( ( NTP4VCLoopInv A C D E F G H ( H - 1 ) m p t L M )
              -> ( NTP4VCExplore A B C D m p t
                ( c e. ( ( NTP4VCMemory L ) X. ( L X. L ) ) |->
                  if ( ( NTP4VCAuxPost L M A B D E F G
                           ( 1st ` c ) ( 1st ` ( 2nd ` c ) )
                           ( 2nd ` ( 2nd ` c ) ) ) , 1 , 0 ) )
                L M ) )
          ) ) /\
        ( ( H - 1 ) < 0 ->
          ( NTP4VCExplore A B C D I J K
            ( c e. ( ( NTP4VCMemory L ) X. ( L X. L ) ) |->
              if ( ( NTP4VCAuxPost L M A B D E F G
                       ( 1st ` c ) ( 1st ` ( 2nd ` c ) )
                       ( 2nd ` ( 2nd ` c ) ) ) , 1 , 0 ) )
            L M ) ) )
    ) $.
$}

${
  $d d g m n p t x y A B C D $.
  ntp4vc-aux-impl-def $a |- ( NTP4VCAuxImpl A B C D ) <-> (
    A. p e. A A. t e. A A. m e. ( NTP4VCMemory A ) (
      ( NTP4VCBS m ) = ( NTP4VCBS D )
      -> A. g e. ( NTP4VCFSet A ) (
        ( NTP4VCAuxPre A B g D C m t )
        -> A. d e. { 0 , 1 } (
          d = if ( t = C , 1 ,
            if ( ( ( NTP4VCCL m ) ` t ) =/= 0 , 1 , 0 ) )
          -> ( ( d = 1 ->
              ( ( NTP4VCUnchanged A C m m ) /\
                ( NTP4VCWell B g D C A ( NTP4VCCL m ) ) /\
                ( ( ( NTP4VCCL m ) ` t ) =/= 0 \/ t = C ) ) )
            /\ ( d =/= 1 ->
              ( t =/= C /\
                ( 0 <_ ( ( NTP4VCBS m ) ` t ) ->
                  ( ( NTP4VCBodyPre m C p t ) /\
                    A. x e. A A. y e. A
                    A. n e. ( NTP4VCMemory A ) (
                      ( NTP4VCBS n ) = ( NTP4VCBS m )
                      -> ( ( NTP4VCBodyNormal A C m p t n x y )
                        -> ( ( ( NTP4VCBS m ) ` t ) =/= 0 ->
                          ( NTP4VCLoopVC B g ( g u. { t } ) D m p t
                            ( ( NTP4VCBS m ) ` t ) n x y A C ) )
                        /\ ( ( ( NTP4VCBS m ) ` t ) = 0 ->
                          ( ( NTP4VCAuxPost A C B g D m p t n x y ) /\
                            -. ( NTP4VCBodyRaises m C p t n ) ) )
                    ) )
                  ) ) ) )
        )
      )
    )
  ) $.
$}

${
  $d x A B C D E $.
  ntp4vc-final-def $a |- ( NTP4VCFinal A B C D E ) <-> (
    ( NTP4VCUnchanged A B C E ) /\
    ( A. x e. A (
        ( ( NTP4VCPath A B C D x ) /\ x =/= B )
        -> ( ( NTP4VCCL E ) ` x ) =/= 0
      ) /\
      A. x e. A (
        ( -. ( NTP4VCPath A B C D x ) /\ x =/= B )
        -> ( ( NTP4VCCL E ) ` x ) = ( ( NTP4VCCL C ) ` x )
      ) )
  ) $.
$}

${
  $d m n p t A B C D E $.
  ntp4vc-main-def $a |- ( NTP4VCMain A B C D E ) <-> (
    ( ( NTP4VCWell C (/) E B A ( NTP4VCCL E ) ) /\ D e. C ) /\
    A. m e. ( NTP4VCMemory A ) (
      ( NTP4VCBS m ) = ( NTP4VCBS E )
      -> ( ( NTP4VCStable A B C (/) E E D m )
        -> ( ( NTP4VCBodyPre m B B D ) /\
          A. p e. A A. t e. A A. n e. ( NTP4VCMemory A ) (
            ( NTP4VCBS n ) = ( NTP4VCBS m )
            -> ( -. ( NTP4VCBodyNormal A B m B D n p t ) /\
              ( ( NTP4VCBodyRaises m B B D n )
                -> ( NTP4VCFinal A B E D n ) ) )
          )
        ) )
    )
  ) $.
$}

${
  $d g i m r x A B $.
  ntp4vc-statement-def $a |- ( NTP4VCStatement A B ) <-> (
    A. r e. A A. g e. ( NTP4VCFSet A )
    A. m e. ( NTP4VCMemory A ) (
      r e. g ->
      ( ( A. x e. A A. i e. ZZ (
          ( ( ( x e. g /\ x =/= B ) /\ 0 <_ i ) /\
              i < ( ( NTP4VCBS m ) ` x ) )
          -> ( ( ( NTP4VCAC m ) ` x ) ` i ) e. g
        ) /\
        A. x e. A ( x e. g -> ( ( NTP4VCCL m ) ` x ) = 0 ) )
      -> ( ( NTP4VCBodyImpl A B m ) /\
        ( ( NTP4VCAuxImpl A g B m ) /\
          ( NTP4VCMain A B g r m ) ) ) )
    )
  ) $.
$}

${
  ntp4vc-loc-nonempty $e |- A =/= (/) $.
  ntp4vc-null-typed $e |- B e. A $.

  ntp4vc-schorr-waite-via-recursion-statement $a |-
    ( NTP4VCStatement A B ) $.
$}
