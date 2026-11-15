$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_memqtvc: the linear-probing membership
  verification condition establishes table occupancy and characterizes the
  abstract membership view at any dummy or matching slot reached after a
  collision-free probe interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U and V are the arbitrary inhabited source carriers key and keym. F is
  keym1, E is the chosen default key used by totalized list lookup, D is
  dummy, H is hash, and B is bucket. Equality and disequality of keys are
  represented by equality and disequality of their F-images, exactly as
  required by eq'spec and neq'spec.

  Finite key lists are represented exactly by Word U. NTP4VCToNat and
  NTP4VCAt are the source integer-to-natural conversion and totalized lookup.
  NTP4VCNumof is the cardinality of positions in the same half-open integer
  interval whose keys are equivalent to dummy under F; this is the unique
  value specified by the source fc and NumOf recursion. Boolean-valued views
  are represented exactly by their truth subsets of V.

  T is the arbitrary inhabited source state carrier. S, L, W, and Q are its
  size, data, view, and loc projections. NTP4VCValid and NTP4VCInvariant
  expand the complete source definitions. Substitution for the source
  let-bound o1, o2, o4, and o5 is definitional. The final assertion retains
  the integer scopes of o3 and j, the complete probe-interval premise, the
  repeated bounds, and both proposition equalities as biconditionals.

  The pinned original Why3 source defines bucket using
  int.ComputerDivision.mod. Under its source premises that the hash is
  nonnegative and the table length is positive, this operation coincides
  with SetMM integer mod, so the definition and both range guarantees are
  preserved exactly. The generated Lean, Rocq, and Isabelle exports are
  secondary references and do not override that source definition. The final
  $a declaration is Metamath's native unproved statement encoding. Every
  preceding $a is syntax or a faithful definition needed to state it; this
  database has no $p proof.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCEq NTP4VCNeq NTP4VCBetween
  NTP4VCNumof NTP4VCValid NTP4VCInvariant
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-eq-syntax $a wff ( NTP4VCEq A B C ) $.
ntp4vc-neq-syntax $a wff ( NTP4VCNeq A B C ) $.
ntp4vc-between-syntax $a wff ( NTP4VCBetween A B C ) $.
ntp4vc-numof-syntax
  $a class ( NTP4VCNumof A B C D E F ) $.
ntp4vc-valid-syntax
  $a wff ( NTP4VCValid A B C D E F G H ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F G H I ) $.

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
  $d a b i j k n p q x y z
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

  $( Source state carrier and projections. $)
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

  $( Source theorem parameters A=x and C=h, followed by fact0. $)
  ntp4vc-x-key $e |- A e. U $.
  ntp4vc-h-state $e |- C e. T $.
  ntp4vc-fact0 $e |- ( NTP4VCNeq F A D ) $.

  ntp4vc-pearl-linear-probing-linear-probing-mem-vc $a |- (
    (
      ( NTP4VCNeq F A D )
      /\
      (
        0 < ( # ` ( L ` C ) )
        /\
        0 <
          (
            NTP4VCNumof
              F ( L ` C ) D E 0 ( # ` ( L ` C ) )
          )
      )
    )
    /\
    A. i e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i < ( # ` ( L ` C ) )
          )
          /\
          (
            (
              NTP4VCEq F
                ( NTP4VCAt ( L ` C ) i E ) D
            )
            \/
            (
              NTP4VCEq F
                ( NTP4VCAt ( L ` C ) i E ) A
            )
          )
          /\
          A. j e. ZZ
            (
              (
                0 <_ j
                /\
                j < ( # ` ( L ` C ) )
              )
              ->
              (
                (
                  NTP4VCBetween
                    (
                      B ` <. A , ( # ` ( L ` C ) ) >.
                    )
                    j i
                )
                ->
                (
                  (
                    NTP4VCNeq F
                      ( NTP4VCAt ( L ` C ) j E ) A
                  )
                  /\
                  (
                    NTP4VCNeq F
                      ( NTP4VCAt ( L ` C ) j E ) D
                  )
                )
              )
            )
        )
        ->
        (
          (
            0 <_ i
            /\
            i < ( # ` ( L ` C ) )
          )
          /\
          (
            (
              (
                NTP4VCNeq F
                  ( NTP4VCAt ( L ` C ) i E ) D
              )
              <->
              (
                (
                  F ` ( NTP4VCAt ( L ` C ) i E )
                ) =/= ( F ` D )
              )
            )
            ->
            (
              (
                NTP4VCNeq F
                  ( NTP4VCAt ( L ` C ) i E ) D
              )
              <->
              ( F ` A ) e. ( W ` C )
            )
          )
        )
      )
  ) $.
$}
