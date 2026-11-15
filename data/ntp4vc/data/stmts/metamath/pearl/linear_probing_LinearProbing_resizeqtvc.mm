$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_resizeqtvc: the linear-probing resize
  verification condition initializes a doubled table, reinserts every
  non-dummy key while preserving probe and location invariants, and establishes
  the resized table state and doubled data length. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U and V are the arbitrary inhabited source carriers key and keym. F is
  keym1, E is the chosen default key used by totalized list lookup, D is
  dummy, H is hash, and B is bucket. Key equality and disequality are equality
  and disequality of F-images, exactly as specified by eq'spec and neq'spec.

  Finite key lists are represented exactly by Word U. NTP4VCToNat,
  NTP4VCAt, NTP4VCSet, and NTP4VCFunUpdate are the source integer-to-natural
  conversion, totalized lookup, List.set, and total function update.
  NTP4VCNumof is the cardinality of positions whose keys are equivalent to
  dummy under F in the same half-open integer interval, the value uniquely
  specified by the source fc and NumOf recursion. Boolean-valued views are
  represented exactly by their truth subsets of V. NTP4VCConstZero is the
  source constant-zero location function.

  NTP4VCValid and NTP4VCInvariant expand the full table and state invariants.
  NTP4VCLocated, NTP4VCResizeContent, NTP4VCProbe,
  NTP4VCResizeStep, and NTP4VCResizeFinal are definitional groupings of the
  source's nested lets, conditionals, loop invariant, insertion step, and
  final state obligation. Proposition-valued conditionals are rendered by
  equivalent pairs of guarded implications. All list, key, state, integer,
  function, and internally quantified witnesses keep their original scopes.

  The pinned original Why3 source defines bucket using
  int.ComputerDivision.mod. Under its source premises that the hash is
  nonnegative and the table length is positive, this operation coincides
  with SetMM integer mod, so the definition and both range guarantees are
  preserved exactly. Generated Lean, Rocq, and Isabelle exports are secondary
  references and do not override the original goal. The final $a declaration
  is Metamath's native unproved statement encoding. Every preceding $a is
  syntax or a faithful definition needed to state it; this database has no
  $p proof.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCFunUpdate NTP4VCConstZero
  NTP4VCEq NTP4VCNeq NTP4VCBetween NTP4VCNumof
  NTP4VCValid NTP4VCInvariant NTP4VCUpdateLaw
  NTP4VCLocated NTP4VCResizeContent NTP4VCProbe
  NTP4VCResizeStep NTP4VCResizeFinal
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-fun-update-syntax
  $a class ( NTP4VCFunUpdate A B C D ) $.
ntp4vc-const-zero-syntax $a class ( NTP4VCConstZero A ) $.

ntp4vc-eq-syntax $a wff ( NTP4VCEq A B C ) $.
ntp4vc-neq-syntax $a wff ( NTP4VCNeq A B C ) $.
ntp4vc-between-syntax $a wff ( NTP4VCBetween A B C ) $.
ntp4vc-numof-syntax $a class ( NTP4VCNumof A B C D E F ) $.
ntp4vc-valid-syntax
  $a wff ( NTP4VCValid A B C D E F G H ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F G H I ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-located-syntax
  $a wff ( NTP4VCLocated A B C D E F G H ) $.
ntp4vc-resize-content-syntax
  $a wff ( NTP4VCResizeContent A B C D E F G H I J K L ) $.
ntp4vc-probe-syntax
  $a wff ( NTP4VCProbe A B C D E F G ) $.
ntp4vc-resize-step-syntax
  $a wff ( NTP4VCResizeStep A B C D E F G H I J K L M ) $.
ntp4vc-resize-final-syntax
  $a wff ( NTP4VCResizeFinal A B C D E F G H I J K L M N O ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

${
  $d k A B C $.

  ntp4vc-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d k A B C D $.

  ntp4vc-fun-update-definition $a |- (
    NTP4VCFunUpdate A B C D
  ) = (
    k e. B |->
      if (
        k = C ,
        D ,
        ( A ` k )
      )
  ) $.
$}

ntp4vc-const-zero-definition $a |- (
  NTP4VCConstZero A
) = ( A X. { 0 } ) $.

ntp4vc-eq-definition $a |- (
  NTP4VCEq A B C
) <-> (
  ( A ` B ) = ( A ` C )
) $.

ntp4vc-neq-definition $a |- (
  NTP4VCNeq A B C
) <-> -.
  ( NTP4VCEq A B C ) $.

ntp4vc-between-definition $a |- (
  NTP4VCBetween A B C
) <-> (
  (
    A <_ B
    /\
    B < C
  )
  \/
  (
    C < A
    /\
    A <_ B
  )
  \/
  (
    B < C
    /\
    C < A
  )
) $.

${
  $d i A B C D E F $.

  ntp4vc-numof-definition $a |- (
    NTP4VCNumof A B C D E F
  ) = (
    # `
    { i e. ( E ..^ F ) |
      ( NTP4VCEq A ( NTP4VCAt B i D ) C ) }
  ) $.
$}

${
  $d i j x A B C D E F G H $.

  ntp4vc-valid-definition $a |- (
    NTP4VCValid A B C D E F G H
  ) <-> (
    -. ( B ` D ) e. G
    /\
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` F )
          )
          ->
          (
            ( NTP4VCNeq B ( NTP4VCAt F i C ) D )
            ->
            (
              ( B ` ( NTP4VCAt F i C ) ) e. G
              /\
              (
                H ` ( B ` ( NTP4VCAt F i C ) )
              ) = i
            )
          )
        )
      /\
      A. x e. A
        (
          ( B ` x ) e. G
          ->
          (
            (
              0 <_ ( H ` ( B ` x ) )
              /\
              ( H ` ( B ` x ) ) < ( # ` F )
            )
            /\
            (
              ( NTP4VCEq B
                  ( NTP4VCAt F ( H ` ( B ` x ) ) C ) x )
              /\
              A. j e. ZZ
                (
                  (
                    0 <_ j
                    /\
                    j < ( # ` F )
                  )
                  ->
                  (
                    (
                      NTP4VCBetween
                        ( E ` <. x , ( # ` F ) >. )
                        j
                        ( H ` ( B ` x ) )
                    )
                    ->
                    (
                      ( NTP4VCNeq B ( NTP4VCAt F j C ) x )
                      /\
                      ( NTP4VCNeq B ( NTP4VCAt F j C ) D )
                    )
                  )
                )
            )
          )
        )
    )
  ) $.
$}

ntp4vc-invariant-definition $a |- (
  NTP4VCInvariant A B C D E F G H I
) <-> (
  0 <_ I
  /\
  (
    I < ( # ` F )
    /\
    (
      (
        I
        +
        ( NTP4VCNumof B F D C 0 ( # ` F ) )
      ) = ( # ` F )
      /\
      ( NTP4VCValid A B C D E F G H )
    )
  )
) $.

${
  $d k A B C D $.

  ntp4vc-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C D
  ) <-> (
    A. k e. ZZ
      (
        (
          0 <_ k
          /\
          k < ( # ` A )
        )
        ->
        (
          ( NTP4VCAt ( NTP4VCSet A B C ) k D )
          =
          if (
            k = B ,
            C ,
            ( NTP4VCAt A k D )
          )
        )
      )
  ) $.
$}

${
  $d k A B C D E F G H $.

  $(
    A=keym1, B=default, C=dummy, D=bucket, E=data, F=table length,
    G=location function, and H=the key whose location is checked.
  $)
  ntp4vc-located-definition $a |- (
    NTP4VCLocated A B C D E F G H
  ) <-> (
    (
      0 <_ ( G ` ( A ` H ) )
      /\
      ( G ` ( A ` H ) ) < F
    )
    /\
    (
      ( NTP4VCEq A
          ( NTP4VCAt E ( G ` ( A ` H ) ) B ) H )
      /\
      A. k e. ZZ
        (
          (
            0 <_ k
            /\
            k < F
          )
          ->
          (
            (
              NTP4VCBetween
                ( D ` <. H , F >. )
                k
                ( G ` ( A ` H ) )
            )
            ->
            (
              ( NTP4VCNeq A ( NTP4VCAt E k B ) H )
              /\
              ( NTP4VCNeq A ( NTP4VCAt E k B ) C )
            )
          )
        )
    )
  ) $.
$}

${
  $d j x A B C D E F G H I J K L $.

  $(
    A=key, B=keym1, C=default, D=dummy, E=bucket,
    F=original data, G=view, H=original loc, I=new table length,
    J=processed source prefix, K=current data, and L=current loc.
  $)
  ntp4vc-resize-content-definition $a |- (
    NTP4VCResizeContent A B C D E F G H I J K L
  ) <-> (
    (
      ( NTP4VCNumof B K D C 0 I )
      =
      (
        ( NTP4VCNumof B F D C 0 J )
        +
        ( I - J )
      )
    )
    /\
    (
      A. j e. ZZ
        (
          (
            0 <_ j
            /\
            j < I
          )
          ->
          (
            ( NTP4VCNeq B ( NTP4VCAt K j C ) D )
            ->
            (
              ( B ` ( NTP4VCAt K j C ) ) e. G
              /\
              (
                L ` ( B ` ( NTP4VCAt K j C ) )
              ) = j
            )
          )
        )
      /\
      A. x e. A
        (
          ( B ` x ) e. G
          ->
          (
            (
              ( H ` ( B ` x ) ) < J
              ->
              ( NTP4VCLocated B C D E K I L x )
            )
            /\
            (
              -. ( H ` ( B ` x ) ) < J
              ->
              A. j e. ZZ
                (
                  (
                    0 <_ j
                    /\
                    j < I
                  )
                  ->
                  ( NTP4VCNeq B ( NTP4VCAt K j C ) x )
                )
            )
          )
        )
    )
  ) $.
$}

${
  $d j k A B C D E F G $.

  $(
    A=keym1, B=default, C=dummy, D=bucket, E=data,
    F=the key to insert, and G=the candidate slot.
  $)
  ntp4vc-probe-definition $a |- (
    NTP4VCProbe A B C D E F G
  ) <-> (
    (
      0 <_ G
      /\
      G < ( # ` E )
    )
    /\
    (
      (
        ( NTP4VCEq A ( NTP4VCAt E G B ) C )
        \/
        ( NTP4VCEq A ( NTP4VCAt E G B ) F )
      )
      /\
      A. k e. ZZ
        (
          (
            0 <_ k
            /\
            k < ( # ` E )
          )
          ->
          (
            (
              NTP4VCBetween
                ( D ` <. F , ( # ` E ) >. )
                k G
            )
            ->
            (
              ( NTP4VCNeq A ( NTP4VCAt E k B ) F )
              /\
              ( NTP4VCNeq A ( NTP4VCAt E k B ) C )
            )
          )
        )
    )
  ) $.
$}

${
  $d j A B C D E F G H I J K L M $.

  $(
    A=key, B=keym, C=keym1, D=default, E=dummy, F=bucket,
    G=original data, H=view, I=original loc, J=new table length,
    K=current source index, L=current data, and M=current loc.
  $)
  ntp4vc-resize-step-definition $a |- (
    NTP4VCResizeStep A B C D E F G H I J K L M
  ) <-> (
    (
      0 <_ K
      /\
      K < ( # ` G )
    )
    /\
    (
      (
        (
          NTP4VCNeq C ( NTP4VCAt G K D ) E
        )
        <->
        (
          ( C ` ( NTP4VCAt G K D ) )
          =/=
          ( C ` E )
        )
      )
      ->
      (
        (
          ( NTP4VCNeq C ( NTP4VCAt G K D ) E )
          ->
          (
            (
              ( NTP4VCNeq C ( NTP4VCAt G K D ) E )
              /\
              (
                0 < ( # ` L )
                /\
                0 <
                  (
                    NTP4VCNumof
                      C L E D 0 ( # ` L )
                  )
              )
            )
            /\
            A. j e. ZZ
              (
                (
                  NTP4VCProbe
                    C D E F L ( NTP4VCAt G K D ) j
                )
                ->
                (
                  (
                    0 <_ j
                    /\
                    j < ( # ` L )
                  )
                  /\
                  (
                    (
                      # `
                      (
                        NTP4VCSet
                          L j ( NTP4VCAt G K D )
                      )
                    ) = ( # ` L )
                    ->
                    (
                      (
                        NTP4VCUpdateLaw
                          L j ( NTP4VCAt G K D ) D
                      )
                      ->
                      (
                        NTP4VCResizeContent
                          A C D E F G H I J
                          ( K + 1 )
                          (
                            NTP4VCSet
                              L j ( NTP4VCAt G K D )
                          )
                          (
                            NTP4VCFunUpdate
                              M B
                              ( C ` ( NTP4VCAt G K D ) )
                              j
                          )
                      )
                    )
                  )
                )
              )
          )
        )
        /\
        (
          -. ( NTP4VCNeq C ( NTP4VCAt G K D ) E )
          ->
          (
            NTP4VCResizeContent
              A C D E F G H I J ( K + 1 ) L M
          )
        )
      )
    )
  ) $.
$}

${
  $d p A B C D E F G H I J K L M N O $.

  $(
    A=key, B=keym1, C=default, D=dummy, E=bucket,
    F=new data, G=view, H=new loc, I=size, J=old data length,
    K=state carrier, and L/M/N/O are size/data/view/loc projections.
  $)
  ntp4vc-resize-final-definition $a |- (
    NTP4VCResizeFinal A B C D E F G H I J K L M N O
  ) <-> (
    A. p e. K
      (
        (
          (
            0 <_ I
            /\
            I < ( # ` F )
          )
          /\
          (
            (
              I
              +
              ( NTP4VCNumof B F D C 0 ( # ` F ) )
            ) = ( # ` F )
            /\
            ( NTP4VCValid A B C D E F G H )
          )
        )
        /\
        (
          (
            H = ( O ` p )
            /\
            (
              G = ( N ` p )
              /\
              (
                F = ( M ` p )
                /\
                I = ( L ` p )
              )
            )
          )
          ->
          (
            ( # ` ( M ` p ) )
            =
            ( 2 x. J )
          )
        )
      )
  ) $.
$}

${
  $d a b i j k l n p q r x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source carriers and chosen inhabitants. $)
  ntp4vc-key-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-key-default $e |- E e. U $.
  ntp4vc-keym-carrier-nonempty $e |- V =/= (/) $.

  $( keym1, hash, dummy, and bucket, including their source specifications. $)
  ntp4vc-keym1-function $e |- F e. ( V ^m U ) $.
  ntp4vc-hash-function $e |- H e. ( ZZ ^m U ) $.

  ntp4vc-hash-nonnegative $e |- A. x e. U
    0 <_ ( H ` x ) $.

  ntp4vc-hash-respects-eq $e |- A. x e. U A. y e. U
    (
      ( NTP4VCEq F x y )
      ->
      ( H ` x ) = ( H ` y )
    ) $.

  ntp4vc-dummy-key $e |- D e. U $.
  ntp4vc-bucket-function
    $e |- B e. ( ZZ ^m ( U X. ZZ ) ) $.

  ntp4vc-bucket-definition $e |- A. n e. ZZ A. x e. U
    (
      0 < n
      ->
      (
        B ` <. x , n >.
      ) = (
        ( H ` x ) mod n
      )
    ) $.

  ntp4vc-bucket-lower-bound $e |- A. n e. ZZ A. x e. U
    (
      0 < n
      ->
      0 <_ ( B ` <. x , n >. )
    ) $.

  ntp4vc-bucket-upper-bound $e |- A. n e. ZZ A. x e. U
    (
      0 < n
      ->
      ( B ` <. x , n >. ) < n
    ) $.

  $( Source state carrier and projections retained from the ambient theory. $)
  ntp4vc-state-carrier-nonempty $e |- T =/= (/) $.
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.
  ntp4vc-data-function
    $e |- L e. ( ( Word U ) ^m T ) $.
  ntp4vc-view-function
    $e |- W e. ( ( ~P V ) ^m T ) $.
  ntp4vc-loc-function
    $e |- Q e. ( ( ZZ ^m V ) ^m T ) $.

  ntp4vc-state-invariant $e |- A. p e. T
    (
      NTP4VCInvariant
        U F E D B
        ( L ` p )
        ( W ` p )
        ( Q ` p )
        ( S ` p )
    ) $.

  ntp4vc-state-extensionality $e |- A. p e. T A. q e. T
    (
      (
        ( S ` p ) = ( S ` q )
        /\
        (
          ( L ` p ) = ( L ` q )
          /\
          (
            ( W ` p ) = ( W ` q )
            /\
            ( Q ` p ) = ( Q ` q )
          )
        )
      )
      ->
      p = q
    ) $.

  $( The sole explicit theorem parameter h. $)
  ntp4vc-resize-state $e |- P e. T $.

  ntp4vc-pearl-linear-probing-linear-probing-resize-vc $a |- (
    0 <_ ( 2 x. ( # ` ( L ` P ) ) )
    /\
    A. a e. Word U
      (
        (
          (
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i < ( 2 x. ( # ` ( L ` P ) ) )
                )
                ->
                ( NTP4VCAt a i E ) = D
              )
          )
          /\
          ( # ` a ) = ( 2 x. ( # ` ( L ` P ) ) )
        )
        ->
        (
          (
            0 <_
              (
                (
                  ( # ` ( L ` P ) ) - 1
                ) + 1
              )
            ->
            (
              (
                NTP4VCResizeContent
                  U F E D B
                  ( L ` P )
                  ( W ` P )
                  ( Q ` P )
                  ( 2 x. ( # ` ( L ` P ) ) )
                  0
                  a
                  ( NTP4VCConstZero V )
              )
              /\
              A. l e. ( ZZ ^m V ) A. b e. Word U
                (
                  ( # ` b ) = ( # ` a )
                  ->
                  (
                    (
                      A. i e. ZZ
                        (
                          (
                            (
                              0 <_ i
                              /\
                              i <_
                                (
                                  ( # ` ( L ` P ) ) - 1
                                )
                            )
                            /\
                            (
                              NTP4VCResizeContent
                                U F E D B
                                ( L ` P )
                                ( W ` P )
                                ( Q ` P )
                                ( 2 x. ( # ` ( L ` P ) ) )
                                i b l
                            )
                          )
                          ->
                          (
                            NTP4VCResizeStep
                              U V F E D B
                              ( L ` P )
                              ( W ` P )
                              ( Q ` P )
                              ( 2 x. ( # ` ( L ` P ) ) )
                              i b l
                          )
                        )
                    )
                    /\
                    (
                      (
                        NTP4VCResizeContent
                          U F E D B
                          ( L ` P )
                          ( W ` P )
                          ( Q ` P )
                          ( 2 x. ( # ` ( L ` P ) ) )
                          (
                            (
                              ( # ` ( L ` P ) ) - 1
                            ) + 1
                          )
                          b l
                      )
                      ->
                      (
                        NTP4VCResizeFinal
                          U F E D B b
                          ( W ` P ) l
                          ( S ` P )
                          ( # ` ( L ` P ) )
                          T S L W Q
                      )
                    )
                  )
                )
            )
          )
          /\
          (
            (
              (
                ( # ` ( L ` P ) ) - 1
              ) + 1
            ) < 0
            ->
            (
              NTP4VCResizeFinal
                U F E D B a
                ( W ` P )
                ( NTP4VCConstZero V )
                ( S ` P )
                ( # ` ( L ` P ) )
                T S L W Q
            )
          )
        )
      )
  ) $.
$}
