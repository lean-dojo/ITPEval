$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_deleteqtvc: the linear-probing deletion
  verification condition advances around the probe table, shifts displaced
  keys when required, preserves the table validity conditions, and maintains
  the number of dummy slots. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U and V are the arbitrary inhabited source carriers key and keym. F is
  keym1, E is the chosen default key used by totalized list lookup, D is
  dummy, H is hash, and B is bucket. Equality and disequality of keys are
  represented by equality and disequality of their F-images, exactly as
  required by eq'spec and neq'spec.

  Finite key lists are represented exactly by Word U. NTP4VCToNat,
  NTP4VCAt, and NTP4VCSet are the source integer-to-natural conversion,
  totalized lookup, and List.set. NTP4VCNumof is the cardinality of positions
  in the same half-open integer interval whose keys are equivalent to dummy
  under F; this is the unique value specified by the source fc and NumOf
  recursion. Boolean-valued views are exactly their truth subsets of V, and
  source Booleans are SetMM's two-element carrier 2 with false = 0 and true =
  1. NTP4VCFunUpdate is ordinary total function update.

  NTP4VCValid expands the complete source table-validity definition.
  NTP4VCDeleteConfig is the conjunction of facts 0 through 13, with its two
  distinguished dummy positions and exceptional probe interval explicit.
  NTP4VCDeleteShift and NTP4VCDeletePost retain the universally quantified
  copy lists, both list-update laws, the updated location function, the
  duplicated new-index bound, the dummy-count implication, and every
  internally quantified Boolean and table witness. Proposition-valued source
  conditionals are rendered by equivalent pairs of guarded implications.

  The pinned original Why3 source defines bucket with
  int.ComputerDivision.mod. For positive table length and nonnegative hash
  values, this is exactly SetMM integer remainder. The Lean Int.tmod and
  Isabelle cmod exports agree on this source meaning; the Rocq Z.quot
  occurrence is a quotient-for-remainder export defect and does not override
  the pinned Why3 goal. The final $a declaration is Metamath's native
  unproved statement encoding. Every preceding $a is syntax or a faithful
  definition needed to state it; this database has no $p proof.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCFunUpdate
  NTP4VCEq NTP4VCNeq NTP4VCBetween NTP4VCNumof
  NTP4VCValid NTP4VCInvariant NTP4VCUpdateLaw
  NTP4VCNext NTP4VCDistance NTP4VCListCopy
  NTP4VCDeleteConfig NTP4VCDeletePost NTP4VCDeleteShift
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-fun-update-syntax
  $a class ( NTP4VCFunUpdate A B C D ) $.

ntp4vc-eq-syntax $a wff ( NTP4VCEq A B C ) $.
ntp4vc-neq-syntax $a wff ( NTP4VCNeq A B C ) $.
ntp4vc-between-syntax $a wff ( NTP4VCBetween A B C ) $.
ntp4vc-numof-syntax
  $a class ( NTP4VCNumof A B C D E F ) $.
ntp4vc-valid-syntax
  $a wff ( NTP4VCValid A B C D E F G H ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F G H I ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-next-syntax $a class ( NTP4VCNext A B ) $.
ntp4vc-distance-syntax $a class ( NTP4VCDistance A B C ) $.
ntp4vc-list-copy-syntax $a wff ( NTP4VCListCopy A B C ) $.
ntp4vc-delete-config-syntax
  $a wff ( NTP4VCDeleteConfig A B C D E F G H I J K ) $.
ntp4vc-delete-post-syntax
  $a wff ( NTP4VCDeletePost A B C D E F G H I ) $.
ntp4vc-delete-shift-syntax
  $a wff ( NTP4VCDeleteShift A B C D E F G H I J K L M N ) $.

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

ntp4vc-next-definition $a |- (
  NTP4VCNext A B
) = if (
  ( B + 1 ) = A ,
  0 ,
  ( B + 1 )
) $.

ntp4vc-distance-definition $a |- (
  NTP4VCDistance A B C
) = if (
  B <_ C ,
  ( ( ( # ` A ) - C ) + B ) ,
  ( B - C )
) $.

${
  $d k A B C $.

  ntp4vc-list-copy-definition $a |- (
    NTP4VCListCopy A B C
  ) <-> (
    ( # ` A ) = ( # ` B )
    /\
    A. k e. ZZ
      (
        (
          0 <_ k
          /\
          k < ( # ` A )
        )
        ->
        (
          ( NTP4VCAt A k C )
          =
          ( NTP4VCAt B k C )
        )
      )
  ) $.
$}

${
  $d k l x A B C D E F G H I J K $.

  $(
    A=key, B=keym1, C=default, D=dummy, E=bucket, F=data,
    G=view, H=loc, I=f0, J=the distinguished dummy slot, and
    K=the current deletion cursor.
  $)
  ntp4vc-delete-config-definition $a |- (
    NTP4VCDeleteConfig A B C D E F G H I J K
  ) <-> (
    (
      0 <_ I
      /\
      I < ( # ` F )
    )
    /\
    (
      (
        0 <_ J
        /\
        J < ( # ` F )
      )
      /\
      (
        (
          0 <_ K
          /\
          K < ( # ` F )
        )
        /\
        (
          J =/= I
          /\
          (
            ( NTP4VCEq B ( NTP4VCAt F J C ) D )
            /\
            (
              ( NTP4VCEq B ( NTP4VCAt F I C ) D )
              /\
              (
                ( NTP4VCBetween J K I )
                /\
                (
                  A. k e. ZZ
                    (
                      (
                        0 <_ k
                        /\
                        k < ( # ` F )
                      )
                      ->
                      (
                        ( NTP4VCBetween K k I )
                        ->
                        (
                          k =/= K
                          ->
                          (
                            NTP4VCNeq B
                              ( NTP4VCAt F k C ) D
                          )
                        )
                      )
                    )
                  /\
                  (
                    -. ( B ` D ) e. G
                    /\
                    (
                      A. k e. ZZ
                        (
                          (
                            0 <_ k
                            /\
                            k < ( # ` F )
                          )
                          ->
                          (
                            (
                              NTP4VCNeq B
                                ( NTP4VCAt F k C ) D
                            )
                            ->
                            (
                              (
                                B ` ( NTP4VCAt F k C )
                              ) e. G
                              /\
                              (
                                H ` (
                                  B ` ( NTP4VCAt F k C )
                                )
                              ) = k
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
                              (
                                H ` ( B ` x )
                              ) < ( # ` F )
                            )
                            /\
                            (
                              (
                                NTP4VCEq B
                                  (
                                    NTP4VCAt F
                                      ( H ` ( B ` x ) ) C
                                  )
                                  x
                              )
                              /\
                              A. l e. ZZ
                                (
                                  (
                                    0 <_ l
                                    /\
                                    l < ( # ` F )
                                  )
                                  ->
                                  (
                                    (
                                      NTP4VCBetween
                                        (
                                          E `
                                          <. x , ( # ` F ) >.
                                        )
                                        l
                                        ( H ` ( B ` x ) )
                                    )
                                    ->
                                    (
                                      (
                                        NTP4VCNeq B
                                          ( NTP4VCAt F l C ) x
                                      )
                                      /\
                                      (
                                        (
                                          NTP4VCNeq B
                                            ( NTP4VCAt F l C ) D
                                        )
                                        \/
                                        (
                                          l = J
                                          /\
                                          (
                                            NTP4VCBetween J K
                                              ( H ` ( B ` x ) )
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
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d a q A B C D E F G H I $.

  $(
    A=key, B=keym, C=keym1, D=default, E=dummy, F=bucket,
    G=the original data, H=the final data, and I=view.
  $)
  ntp4vc-delete-post-definition $a |- (
    NTP4VCDeletePost A B C D E F G H I
  ) <-> (
    A. q e. ( ZZ ^m B )
      A. a e. Word A
        (
          ( # ` a ) = ( # ` H )
          ->
          (
            (
              (
                NTP4VCNumof
                  C a E D 0 ( # ` a )
              )
              =
              (
                NTP4VCNumof
                  C H E D 0 ( # ` a )
              )
              /\
              ( NTP4VCValid A C D E F a I q )
            )
            ->
            (
              (
                NTP4VCNumof
                  C a E D 0 ( # ` a )
              )
              =
              (
                NTP4VCNumof
                  C G E D 0 ( # ` a )
              )
              /\
              ( NTP4VCValid A C D E F a I q )
            )
          )
        )
  ) $.
$}

${
  $d a b A B C D E F G H I J K L M N $.

  $(
    A=key, B=keym, C=keym1, D=default, E=dummy, F=bucket,
    G=original data, H=view, I=loc, J=f0, K=j, L=i,
    M=i1, and N=xi.
  $)
  ntp4vc-delete-shift-definition $a |- (
    NTP4VCDeleteShift A B C D E F G H I J K L M N
  ) <-> (
    A. a e. Word A
      (
        ( NTP4VCListCopy a G D )
        ->
        (
          (
            0 <_ K
            /\
            K < ( # ` G )
          )
          /\
          (
            (
              # ` ( NTP4VCSet G K N )
            ) = ( # ` G )
            ->
            (
              ( NTP4VCUpdateLaw G K N D )
              ->
              A. b e. Word A
                (
                  (
                    NTP4VCListCopy
                      b ( NTP4VCSet G K N ) D
                  )
                  ->
                  (
                    (
                      0 <_ M
                      /\
                      M < ( # ` ( NTP4VCSet G K N ) )
                    )
                    /\
                    (
                      (
                        # `
                        (
                          NTP4VCSet
                            ( NTP4VCSet G K N ) M E
                        )
                      )
                      =
                      ( # ` ( NTP4VCSet G K N ) )
                      ->
                      (
                        (
                          NTP4VCUpdateLaw
                            ( NTP4VCSet G K N ) M E D
                        )
                        ->
                        (
                          (
                            0 <_ ( NTP4VCDistance G J L )
                            /\
                            (
                              NTP4VCDistance
                                (
                                  NTP4VCSet
                                    ( NTP4VCSet G K N ) M E
                                )
                                J M
                            )
                            <
                            ( NTP4VCDistance G J L )
                          )
                          /\
                          (
                            (
                              0 <_ M
                              /\
                              M <
                                (
                                  # `
                                  (
                                    NTP4VCSet
                                      ( NTP4VCSet G K N ) M E
                                  )
                                )
                            )
                            /\
                            (
                              (
                                NTP4VCDeleteConfig
                                  A C D E F
                                  (
                                    NTP4VCSet
                                      ( NTP4VCSet G K N ) M E
                                  )
                                  H
                                  (
                                    NTP4VCFunUpdate
                                      I B ( C ` N ) K
                                  )
                                  J M M
                              )
                              /\
                              (
                                NTP4VCDeletePost
                                  A B C D E F
                                  G
                                  (
                                    NTP4VCSet
                                      ( NTP4VCSet G K N ) M E
                                  )
                                  H
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
        )
      )
  ) $.
$}

${
  $d a b c d i j k l n p q r x y z
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

  $(
    Source theorem parameters:
    A=f0, C=a, G=j, I=i, J=view1, and K=loc1.
    The single configuration hypothesis is definitionally the conjunction of
    source facts fact0 through fact13.
  $)
  ntp4vc-f0-integer $e |- A e. ZZ $.
  ntp4vc-input-data $e |- C e. Word U $.
  ntp4vc-j-integer $e |- G e. ZZ $.
  ntp4vc-i-integer $e |- I e. ZZ $.
  ntp4vc-view1-subset $e |- J C_ V $.
  ntp4vc-loc1-function $e |- K e. ( ZZ ^m V ) $.

  ntp4vc-delete-facts $e |- (
    NTP4VCDeleteConfig U F E D B C J K A G I
  ) $.

  ntp4vc-pearl-linear-probing-linear-probing-delete-vc $a |- (
    (
      0 <_ ( NTP4VCNext ( # ` C ) I )
      /\
      ( NTP4VCNext ( # ` C ) I ) < ( # ` C )
    )
    /\
    (
      (
        (
          NTP4VCNeq F
            (
              NTP4VCAt C
                ( NTP4VCNext ( # ` C ) I ) E
            )
            D
        )
        <->
        (
          (
            F `
            (
              NTP4VCAt C
                ( NTP4VCNext ( # ` C ) I ) E
            )
          )
          =/=
          ( F ` D )
        )
      )
      ->
      (
        (
          (
            NTP4VCNeq F
              (
                NTP4VCAt C
                  ( NTP4VCNext ( # ` C ) I ) E
              )
              D
          )
          ->
          (
            0 < ( # ` C )
            /\
            (
              (
                0 <_
                  (
                    B `
                    <.
                      (
                        NTP4VCAt C
                          ( NTP4VCNext ( # ` C ) I ) E
                      ) ,
                      ( # ` C )
                    >.
                  )
                /\
                (
                  B `
                  <.
                    (
                      NTP4VCAt C
                        ( NTP4VCNext ( # ` C ) I ) E
                    ) ,
                    ( # ` C )
                  >.
                ) < ( # ` C )
              )
              ->
              A. b e. 2
                (
                  b
                  =
                  if (
                    G
                    <
                    (
                      B `
                      <.
                        (
                          NTP4VCAt C
                            ( NTP4VCNext ( # ` C ) I ) E
                        ) ,
                        ( # ` C )
                      >.
                    ) ,
                    if (
                      (
                        B `
                        <.
                          (
                            NTP4VCAt C
                              ( NTP4VCNext ( # ` C ) I ) E
                          ) ,
                          ( # ` C )
                        >.
                      )
                      <_
                      ( NTP4VCNext ( # ` C ) I ) ,
                      1 ,
                      0
                    ) ,
                    0
                  )
                  ->
                  A. c e. 2
                    (
                      (
                        (
                          b = 1
                          ->
                          c = 1
                        )
                        /\
                        (
                          b =/= 1
                          ->
                          E. d e. 2
                            (
                              d
                              =
                              if (
                                (
                                  NTP4VCNext
                                    ( # ` C ) I
                                ) < G ,
                                if (
                                  G
                                  <
                                  (
                                    B `
                                    <.
                                      (
                                        NTP4VCAt C
                                          (
                                            NTP4VCNext
                                              ( # ` C ) I
                                          )
                                          E
                                      ) ,
                                      ( # ` C )
                                    >.
                                  ) ,
                                  1 ,
                                  0
                                ) ,
                                0
                              )
                              /\
                              c
                              =
                              if (
                                d = 1 ,
                                1 ,
                                if (
                                  (
                                    B `
                                    <.
                                      (
                                        NTP4VCAt C
                                          (
                                            NTP4VCNext
                                              ( # ` C ) I
                                          )
                                          E
                                      ) ,
                                      ( # ` C )
                                    >.
                                  )
                                  <_
                                  (
                                    NTP4VCNext
                                      ( # ` C ) I
                                  ) ,
                                  if (
                                    (
                                      NTP4VCNext
                                        ( # ` C ) I
                                    ) < G ,
                                    1 ,
                                    0
                                  ) ,
                                  0
                                )
                              )
                            )
                        )
                      )
                      ->
                      (
                        (
                          c = 1
                          ->
                          (
                            0 <_
                              (
                                NTP4VCDistance C A I
                              )
                            /\
                            (
                              (
                                NTP4VCDistance C A
                                  (
                                    NTP4VCNext
                                      ( # ` C ) I
                                  )
                              )
                              <
                              (
                                NTP4VCDistance C A I
                              )
                              /\
                              (
                                NTP4VCDeleteConfig
                                  U F E D B C J K A G
                                  (
                                    NTP4VCNext
                                      ( # ` C ) I
                                  )
                              )
                            )
                          )
                        )
                        /\
                        (
                          c =/= 1
                          ->
                          (
                            NTP4VCDeleteShift
                              U V F E D B C J K A G I
                              (
                                NTP4VCNext
                                  ( # ` C ) I
                              )
                              (
                                NTP4VCAt C
                                  (
                                    NTP4VCNext
                                      ( # ` C ) I
                                  )
                                  E
                              )
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
          -.
          (
            NTP4VCNeq F
              (
                NTP4VCAt C
                  ( NTP4VCNext ( # ` C ) I ) E
              )
              D
          )
          ->
          ( NTP4VCValid U F E D B C J K )
        )
      )
    )
  ) $.
$}
