$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2015_dancing_links_DancingLinks_removeqtvc: the dancing
  links removal verification condition, relating two neighbor-array updates
  to removal of one node from a valid circular list. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat
  reproduces the exported Int.toNat conversion, NTP4VCAt is integer-indexed
  lookup with default zero outside [0, length), and NTP4VCSet, NTP4VCNth, and
  NTP4VCFunUpdate reproduce List.set, integer-indexed lookup, and
  Function.update.

  D is the arbitrary nonempty source carrier dll; P, Q, and R are its prev,
  next, and n fields. Their total function types, the equal-length/size
  invariant, and record extensionality law are explicit scoped hypotheses.
  NTP4VCValidIn, NTP4VCValidOut, and NTP4VCIsList are the complete source
  predicates, including the circular predecessor/successor equations and
  the internal universal distinctness condition.

  NTP4VCAllResults preserves the universal quantifier over every candidate
  post-state object, both repeated update-length antecedents, the pointwise
  function-update antecedent, the reconstructed invariant, and the
  implication yielding valid_out and is_list. NTP4VCConclusion expands every
  source let-binding by substitution while retaining all generated bounds,
  nested implications, and both ordered list updates.

  Splitting the typed parameters, source context, and two theorem assumptions
  into scoped essential hypotheses is the curried Metamath sequent
  corresponding to the Why3 verification condition. Every auxiliary $a is
  syntax or a faithful definition. The final $a declaration is Metamath's
  native unproved statement encoding, and this database contains no $p
  declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCNth NTP4VCFunUpdate
  NTP4VCBound NTP4VCValidIn NTP4VCValidOut NTP4VCIsList
  NTP4VCSetFunction NTP4VCAllResults NTP4VCConclusion
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.
ntp4vc-nth-syntax
  $a class ( NTP4VCNth A ) $.
ntp4vc-fun-update-syntax
  $a class ( NTP4VCFunUpdate A B C ) $.

ntp4vc-bound-syntax
  $a wff ( NTP4VCBound A B ) $.
ntp4vc-valid-in-syntax
  $a wff ( NTP4VCValidIn A B C D E ) $.
ntp4vc-valid-out-syntax
  $a wff ( NTP4VCValidOut A B C D E ) $.
ntp4vc-is-list-syntax
  $a wff ( NTP4VCIsList A B C D E ) $.
ntp4vc-set-function-syntax
  $a wff ( NTP4VCSetFunction A B C ) $.
ntp4vc-all-results-syntax
  $a wff ( NTP4VCAllResults A B C D E F G H I J ) $.
ntp4vc-conclusion-syntax
  $a wff ( NTP4VCConclusion A B C D E F G ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( 0 <_ B /\ B < ( # ` A ) ) ,
  ( A ` B ) ,
  0
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
  $d k A $.

  ntp4vc-nth-definition $a |- (
    NTP4VCNth A
  ) = (
    k e. ZZ |->
      ( NTP4VCAt A k )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-fun-update-definition $a |- (
    NTP4VCFunUpdate A B C
  ) = (
    k e. ZZ |->
      if (
        k = B ,
        C ,
        ( A ` k )
      )
  ) $.
$}

ntp4vc-bound-definition $a |- (
  NTP4VCBound A B
) <->
(
  0 <_ B
  /\
  B < ( # ` A )
) $.

ntp4vc-valid-in-definition $a |- (
  NTP4VCValidIn A B C D E
) <->
(
  (
    0 <_ E
    /\
    E < ( C ` D )
  )
  /\
  (
    (
      0 <_ ( NTP4VCAt ( A ` D ) E )
      /\
      ( NTP4VCAt ( A ` D ) E ) < ( C ` D )
    )
    /\
    (
      (
        0 <_ ( NTP4VCAt ( B ` D ) E )
        /\
        ( NTP4VCAt ( B ` D ) E ) < ( C ` D )
      )
      /\
      (
        (
          NTP4VCAt
            ( B ` D )
            ( NTP4VCAt ( A ` D ) E )
        )
        =
        E
        /\
        (
          NTP4VCAt
            ( A ` D )
            ( NTP4VCAt ( B ` D ) E )
        )
        =
        E
      )
    )
  )
) $.

ntp4vc-valid-out-definition $a |- (
  NTP4VCValidOut A B C D E
) <->
(
  (
    0 <_ E
    /\
    E < ( C ` D )
  )
  /\
  (
    (
      0 <_ ( NTP4VCAt ( A ` D ) E )
      /\
      ( NTP4VCAt ( A ` D ) E ) < ( C ` D )
    )
    /\
    (
      (
        0 <_ ( NTP4VCAt ( B ` D ) E )
        /\
        ( NTP4VCAt ( B ` D ) E ) < ( C ` D )
      )
      /\
      (
        (
          NTP4VCAt
            ( B ` D )
            ( NTP4VCAt ( A ` D ) E )
        )
        =
        ( NTP4VCAt ( B ` D ) E )
        /\
        (
          NTP4VCAt
            ( A ` D )
            ( NTP4VCAt ( B ` D ) E )
        )
        =
        ( NTP4VCAt ( A ` D ) E )
      )
    )
  )
) $.

${
  $d k k' A B C D E $.

  ntp4vc-is-list-definition $a |- (
    NTP4VCIsList A B C D E
  ) <->
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
          0 <_ ( NTP4VCAt E k )
          /\
          ( NTP4VCAt E k ) < ( C ` D )
        )
        /\
        (
          (
            NTP4VCAt
              ( A ` D )
              ( NTP4VCAt E k )
          )
          =
          (
            NTP4VCAt
              E
              if (
                k = 0 ,
                ( ( # ` E ) - 1 ) ,
                ( k - 1 )
              )
          )
          /\
          (
            (
              NTP4VCAt
                ( B ` D )
                ( NTP4VCAt E k )
            )
            =
            (
              NTP4VCAt
                E
                if (
                  k = ( ( # ` E ) - 1 ) ,
                  0 ,
                  ( k + 1 )
                )
            )
            /\
            A. k' e. ZZ
              (
                (
                  0 <_ k'
                  /\
                  k' < ( # ` E )
                )
                ->
                (
                  -. k = k'
                  ->
                  -. ( NTP4VCAt E k ) = ( NTP4VCAt E k' )
                )
              )
          )
        )
      )
    ) $.
$}

ntp4vc-set-function-definition $a |- (
  NTP4VCSetFunction A B C
) <->
(
  ( NTP4VCNth ( NTP4VCSet A B C ) )
  =
  (
    NTP4VCFunUpdate
      ( NTP4VCNth A )
      B
      C
  )
) $.

${
  $d x A B C D E F G H I J $.

  ntp4vc-all-results-definition $a |- (
    NTP4VCAllResults A B C D E F G H I J
  ) <->
  A. x e. D
    (
      (
        ( # ` ( NTP4VCSet ( B ` E ) I J ) )
        =
        ( # ` ( B ` E ) )
      )
      ->
      (
        (
          ( # ` ( NTP4VCSet ( B ` E ) I J ) )
          =
          ( # ` ( B ` E ) )
        )
        ->
        (
          ( NTP4VCSetFunction ( B ` E ) I J )
          ->
          (
            (
              ( # ` H )
              =
              ( # ` ( NTP4VCSet ( B ` E ) I J ) )
              /\
              ( # ` ( NTP4VCSet ( B ` E ) I J ) )
              =
              ( C ` E )
            )
            /\
            (
              (
                ( C ` E ) = ( C ` x )
                /\
                (
                  ( NTP4VCSet ( B ` E ) I J ) = ( B ` x )
                  /\
                  H = ( A ` x )
                )
              )
              ->
              (
                ( NTP4VCValidOut A B C x F )
                /\
                ( NTP4VCIsList A B C x G )
              )
            )
          )
        )
      )
    ) $.
$}

ntp4vc-conclusion-definition $a |- (
  NTP4VCConclusion A B C D E F G
) <->
(
  ( NTP4VCBound ( A ` E ) F )
  /\
  (
    ( NTP4VCBound ( B ` E ) F )
    /\
    (
      (
        NTP4VCBound
          ( A ` E )
          ( NTP4VCAt ( B ` E ) F )
      )
      /\
      (
        (
          ( # `
            (
              NTP4VCSet
                ( A ` E )
                ( NTP4VCAt ( B ` E ) F )
                ( NTP4VCAt ( A ` E ) F )
            )
          )
          =
          ( # ` ( A ` E ) )
        )
        ->
        (
          (
            ( # `
              (
                NTP4VCSet
                  ( A ` E )
                  ( NTP4VCAt ( B ` E ) F )
                  ( NTP4VCAt ( A ` E ) F )
              )
            )
            =
            ( # ` ( A ` E ) )
          )
          ->
          (
            (
              NTP4VCSetFunction
                ( A ` E )
                ( NTP4VCAt ( B ` E ) F )
                ( NTP4VCAt ( A ` E ) F )
            )
            ->
            (
              ( NTP4VCBound ( B ` E ) F )
              /\
              (
                NTP4VCBound
                  (
                    NTP4VCSet
                      ( A ` E )
                      ( NTP4VCAt ( B ` E ) F )
                      ( NTP4VCAt ( A ` E ) F )
                  )
                  F
                /\
                (
                  (
                    NTP4VCBound
                      ( B ` E )
                      (
                        NTP4VCAt
                          (
                            NTP4VCSet
                              ( A ` E )
                              ( NTP4VCAt ( B ` E ) F )
                              ( NTP4VCAt ( A ` E ) F )
                          )
                          F
                      )
                  )
                  /\
                  (
                    NTP4VCAllResults
                      A B C D E F G
                      (
                        NTP4VCSet
                          ( A ` E )
                          ( NTP4VCAt ( B ` E ) F )
                          ( NTP4VCAt ( A ` E ) F )
                      )
                      (
                        NTP4VCAt
                          (
                            NTP4VCSet
                              ( A ` E )
                              ( NTP4VCAt ( B ` E ) F )
                              ( NTP4VCAt ( A ` E ) F )
                          )
                          F
                      )
                      ( NTP4VCAt ( B ` E ) F )
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

${
  $d k k' x y
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source context: D=dll, P=prev, Q=next, and R=n. $)
  ntp4vc-dll-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-prev-function $e |- P e. ( ( Word ZZ ) ^m D ) $.
  ntp4vc-next-function $e |- Q e. ( ( Word ZZ ) ^m D ) $.
  ntp4vc-n-function $e |- R e. ( ZZ ^m D ) $.

  ntp4vc-dll-invariant $e |- A. x e. D
    (
      ( # ` ( P ` x ) ) = ( # ` ( Q ` x ) )
      /\
      ( # ` ( Q ` x ) ) = ( R ` x )
    ) $.

  ntp4vc-dll-injective $e |- A. x e. D A. y e. D
    (
      (
        ( P ` x ) = ( P ` y )
        /\
        (
          ( Q ` x ) = ( Q ` y )
          /\
          ( R ` x ) = ( R ` y )
        )
      )
      ->
      x = y
    ) $.

  $( Source theorem parameters l, i, and s, followed by fact0 and fact1. $)
  ntp4vc-l-dll $e |- A e. D $.
  ntp4vc-i-integer $e |- B e. ZZ $.
  ntp4vc-s-list $e |- C e. Word ZZ $.
  ntp4vc-fact0 $e |- ( NTP4VCValidIn P Q R A B ) $.
  ntp4vc-fact1 $e |- (
    NTP4VCIsList P Q R A ( <" B "> ++ C )
  ) $.

  ntp4vc-pearl-verifythis-2015-dancing-links-dancinglinks-remove-vc
    $a |- ( NTP4VCConclusion P Q R D A B C ) $.
$}
