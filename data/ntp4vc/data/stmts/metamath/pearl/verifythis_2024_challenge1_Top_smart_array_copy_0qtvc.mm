$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2024_challenge1_Top_smart_array_copy_0qtvc
  (ntp4vc__metamath__pearl/verifythis_2024_challenge1_Top_smart_array_copy_0qtvc):
  the Smart Array Copy 0 verification condition for copying shuffled
  fixed-size subsegments element by element and then copying a final
  remainder while preserving all loop invariants. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary inhabited source element type is represented by a nonempty
  SetMM carrier, and its arrays are represented exactly by arbitrary finite
  words over that carrier. Integer permutation arrays are Word ZZ.
  NTP4VCToNat, NTP4VCAt, and NTP4VCSet reproduce Int.toNat, totalized list
  lookup, and List.set. NTP4VCSetLaw is the generated full-integer-domain
  Function.update equality.

  NTP4VCValidChunk, NTP4VCCopy, NTP4VCPermutation, and
  NTP4VCPermutationPair are direct biconditional definitions of the source
  predicates. The remaining predicates only factor the generated outer
  loop, shuffled-subsegment loop, element-copy loop, and remainder loop.
  Expanding their definitions recovers every integer and array quantifier,
  length premise, bound, invariant, update premise, implication, and
  conclusion. Source let-bound values are replaced only by their defining
  expressions. Splitting the typed parameters and eight assumptions into
  scoped essential hypotheses is bidirectionally equivalent to the source
  curried theorem.

  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCSetLaw
  NTP4VCValidChunk NTP4VCCopy
  NTP4VCPermutation NTP4VCPermutationPair
  NTP4VCInnerInv NTP4VCElementInv NTP4VCElementStep
  NTP4VCElementLoop NTP4VCInnerStep NTP4VCInnerLoop
  NTP4VCOuterStep NTP4VCTailInv NTP4VCTailStep
  NTP4VCTail NTP4VCMain
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-set-law-syntax
  $a wff ( NTP4VCSetLaw A B C D ) $.
ntp4vc-valid-chunk-syntax
  $a wff ( NTP4VCValidChunk A B C ) $.
ntp4vc-copy-syntax
  $a wff ( NTP4VCCopy A B C D E ) $.
ntp4vc-permutation-syntax
  $a wff ( NTP4VCPermutation A B ) $.
ntp4vc-permutation-pair-syntax
  $a wff ( NTP4VCPermutationPair A B C ) $.
ntp4vc-inner-inv-syntax
  $a wff ( NTP4VCInnerInv A B C D E F G H ) $.
ntp4vc-element-inv-syntax
  $a wff ( NTP4VCElementInv A B C D E F G H I ) $.
ntp4vc-element-step-syntax
  $a wff ( NTP4VCElementStep A B C D E F G H I J ) $.
ntp4vc-element-loop-syntax
  $a wff ( NTP4VCElementLoop A B C D E F G H I ) $.
ntp4vc-inner-step-syntax
  $a wff ( NTP4VCInnerStep A B C D E F G H I ) $.
ntp4vc-inner-loop-syntax
  $a wff ( NTP4VCInnerLoop A B C D E F G H ) $.
ntp4vc-outer-step-syntax
  $a wff ( NTP4VCOuterStep A B C D E F G ) $.
ntp4vc-tail-inv-syntax
  $a wff ( NTP4VCTailInv A B C D E F G ) $.
ntp4vc-tail-step-syntax
  $a wff ( NTP4VCTailStep A B C D E F G H ) $.
ntp4vc-tail-syntax
  $a wff ( NTP4VCTail A B C D E F G H I ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCMain A B C D E F G H ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

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
  $d q A B C D $.

  ntp4vc-set-law-definition $a |- (
    NTP4VCSetLaw A B C D
  ) <->
  A. q e. ZZ
    (
      ( NTP4VCAt ( NTP4VCSet A B C ) q D )
      =
      if (
        q = B ,
        C ,
        ( NTP4VCAt A q D )
      )
    ) $.
$}

ntp4vc-valid-chunk-definition $a |- (
  NTP4VCValidChunk A B C
) <->
(
  0 <_ B
  /\
  (
    B <_ ( B + C )
    /\
    ( B + C ) <_ ( # ` A )
  )
) $.

${
  $d i A B C D E $.

  ntp4vc-copy-definition $a |- (
    NTP4VCCopy A B C D E
  ) <->
  (
    ( NTP4VCValidChunk A C D )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. i e. ZZ
        (
          (
            C <_ i
            /\
            i < ( C + D )
          )
          ->
          (
            ( NTP4VCAt B i E )
            =
            ( NTP4VCAt A i E )
          )
        )
    )
  ) $.
$}

${
  $d i j A B $.

  ntp4vc-permutation-definition $a |- (
    NTP4VCPermutation A B
  ) <->
  (
    (
      0 <_ A
      /\
      A <_ ( # ` B )
    )
    /\
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < A
          )
          ->
          (
            0 <_ ( NTP4VCAt B i 0 )
            /\
            ( NTP4VCAt B i 0 ) < A
          )
        )
      /\
      A. i e. ZZ
        A. j e. ZZ
          (
            (
              0 <_ i
              /\
              i < A
            )
            ->
            (
              (
                0 <_ j
                /\
                j < A
              )
              ->
              (
                i =/= j
                ->
                ( NTP4VCAt B i 0 )
                  =/= ( NTP4VCAt B j 0 )
              )
            )
          )
    )
  ) $.
$}

${
  $d i A B C $.

  ntp4vc-permutation-pair-definition $a |- (
    NTP4VCPermutationPair A B C
  ) <->
  (
    ( NTP4VCPermutation A B )
    /\
    (
      ( NTP4VCPermutation A C )
      /\
      (
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < A
            )
            ->
            (
              NTP4VCAt
                B
                ( NTP4VCAt C i 0 )
                0
            )
            =
            i
          )
        /\
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < A
            )
            ->
            (
              NTP4VCAt
                C
                ( NTP4VCAt B i 0 )
                0
            )
            =
            i
          )
      )
    )
  ) $.
$}

$( A=src, B=dst, C=sigma, D=k, E=l, F=s, G=j, H=default. $)
${
  $d j A B C D E F G H $.

  ntp4vc-inner-inv-definition $a |- (
    NTP4VCInnerInv A B C D E F G H
  ) <->
  (
    ( NTP4VCCopy A B 0 ( F * ( D * E ) ) H )
    /\
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < G
        )
        ->
        (
          NTP4VCCopy
            A
            B
            (
              ( F * ( D * E ) )
              +
              ( ( NTP4VCAt C j 0 ) * D )
            )
            D
            H
        )
      )
  ) $.
$}

$( A=src, B=dst, C=sigma, D=k, E=l, F=s, G=j, H=i,
   I=default. $)
ntp4vc-element-inv-definition $a |- (
  NTP4VCElementInv A B C D E F G H I
) <->
(
  ( NTP4VCInnerInv A B C D E F G I )
  /\
  (
    NTP4VCCopy
      A
      B
      (
        ( F * ( D * E ) )
        +
        ( ( NTP4VCAt C G 0 ) * D )
      )
      H
      I
  )
) $.

$( A=carrier, B=default, C=src, D=dst3, E=sigma,
   F=k, G=l, H=s, I=j, J=i. $)
ntp4vc-element-step-definition $a |- (
  NTP4VCElementStep A B C D E F G H I J
) <->
(
  (
    0 <_
      (
        (
          ( H * ( F * G ) )
          +
          ( ( NTP4VCAt E I 0 ) * F )
        )
        + J
      )
    /\
    (
      (
        (
          ( H * ( F * G ) )
          +
          ( ( NTP4VCAt E I 0 ) * F )
        )
        + J
      )
      < ( # ` C )
    )
  )
  /\
  (
    (
      0 <_
        (
          (
            ( H * ( F * G ) )
            +
            ( ( NTP4VCAt E I 0 ) * F )
          )
          + J
        )
      /\
      (
        (
          (
            ( H * ( F * G ) )
            +
            ( ( NTP4VCAt E I 0 ) * F )
          )
          + J
        )
        < ( # ` D )
      )
    )
    /\
    (
      (
        # `
        (
          NTP4VCSet
            D
            (
              (
                ( H * ( F * G ) )
                +
                ( ( NTP4VCAt E I 0 ) * F )
              )
              + J
            )
            (
              NTP4VCAt
                C
                (
                  (
                    ( H * ( F * G ) )
                    +
                    ( ( NTP4VCAt E I 0 ) * F )
                  )
                  + J
                )
                B
            )
        )
      )
      =
      ( # ` D )
      ->
      (
        (
          NTP4VCSetLaw
            D
            (
              (
                ( H * ( F * G ) )
                +
                ( ( NTP4VCAt E I 0 ) * F )
              )
              + J
            )
            (
              NTP4VCAt
                C
                (
                  (
                    ( H * ( F * G ) )
                    +
                    ( ( NTP4VCAt E I 0 ) * F )
                  )
                  + J
                )
                B
            )
            B
        )
        ->
        (
          NTP4VCElementInv
            C
            (
              NTP4VCSet
                D
                (
                  (
                    ( H * ( F * G ) )
                    +
                    ( ( NTP4VCAt E I 0 ) * F )
                  )
                  + J
                )
                (
                  NTP4VCAt
                    C
                    (
                      (
                        ( H * ( F * G ) )
                        +
                        ( ( NTP4VCAt E I 0 ) * F )
                      )
                      + J
                    )
                    B
                )
            )
            E F G H I ( J + 1 ) B
        )
      )
    )
  )
) $.

$( A=carrier, B=default, C=src, D=dst2, E=sigma,
   F=k, G=l, H=s, I=j. $)
${
  $d i x A B C D E F G H I $.

  ntp4vc-element-loop-definition $a |- (
    NTP4VCElementLoop A B C D E F G H I
  ) <->
  (
    (
      (
        0 <_ ( ( F - 1 ) + 1 )
        ->
        (
          ( NTP4VCElementInv C D E F G H I 0 B )
          /\
          A. x e. Word A
            (
              ( # ` x ) = ( # ` D )
              ->
              (
                A. i e. ZZ
                  (
                    (
                      (
                        0 <_ i
                        /\
                        i <_ ( F - 1 )
                      )
                      /\
                      (
                        NTP4VCElementInv
                          C x E F G H I i B
                      )
                    )
                    ->
                    (
                      NTP4VCElementStep
                        A B C x E F G H I i
                    )
                  )
                /\
                (
                  (
                    NTP4VCElementInv
                      C x E F G H I ( ( F - 1 ) + 1 ) B
                  )
                  ->
                  (
                    NTP4VCInnerInv
                      C x E F G H ( I + 1 ) B
                  )
                )
              )
            )
        )
      )
      /\
      (
        ( ( F - 1 ) + 1 ) < 0
        ->
        (
          NTP4VCInnerInv
            C D E F G H ( I + 1 ) B
        )
      )
    )
  ) $.
$}

$( A=carrier, B=default, C=src, D=dst2, E=sigma,
   F=k, G=l, H=s, I=j. $)
ntp4vc-inner-step-definition $a |- (
  NTP4VCInnerStep A B C D E F G H I
) <->
(
  (
    0 <_ I
    /\
    I < ( # ` E )
  )
  /\
  (
    NTP4VCElementLoop
      A B C D E F G H I
  )
) $.

$( A=carrier, B=default, C=src, D=dst1, E=sigma,
   F=k, G=l, H=s. $)
${
  $d j x A B C D E F G H $.

  ntp4vc-inner-loop-definition $a |- (
    NTP4VCInnerLoop A B C D E F G H
  ) <->
  (
    (
      0 <_ ( ( G - 1 ) + 1 )
      ->
      (
        ( NTP4VCInnerInv C D E F G H 0 B )
        /\
        A. x e. Word A
          (
            ( # ` x ) = ( # ` D )
            ->
            (
              A. j e. ZZ
                (
                  (
                    (
                      0 <_ j
                      /\
                      j <_ ( G - 1 )
                    )
                    /\
                    (
                      NTP4VCInnerInv
                        C x E F G H j B
                    )
                  )
                  ->
                  (
                    NTP4VCInnerStep
                      A B C x E F G H j
                  )
                )
              /\
              (
                (
                  NTP4VCInnerInv
                    C x E F G H ( ( G - 1 ) + 1 ) B
                )
                ->
                (
                  NTP4VCCopy
                    C x 0 ( ( H + 1 ) * ( F * G ) ) B
                )
              )
            )
          )
      )
    )
    /\
    (
      ( ( G - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCCopy
          C D 0 ( ( H + 1 ) * ( F * G ) ) B
      )
    )
  ) $.
$}

$( A=carrier, B=default, C=src, D=dst1, E=k, F=l, G=s. $)
${
  $d p u A B C D E F G $.

  ntp4vc-outer-step-definition $a |- (
    NTP4VCOuterStep A B C D E F G
  ) <->
  (
    0 < F
    /\
    A. p e. Word ZZ
      A. u e. Word ZZ
        (
          (
            (
              ( # ` p ) = ( # ` u )
              /\
              ( # ` u ) = F
            )
            /\
            ( NTP4VCPermutationPair F p u )
          )
          ->
          (
            NTP4VCInnerLoop
              A B C D p E F G
          )
        )
  ) $.
$}

$( A=src, B=dst, C=k, D=l, E=q, F=i, G=default. $)
ntp4vc-tail-inv-definition $a |- (
  NTP4VCTailInv A B C D E F G
) <->
(
  ( NTP4VCCopy A B 0 ( E * ( C * D ) ) G )
  /\
  (
    NTP4VCCopy
      A B
      ( E * ( C * D ) )
      F
      G
  )
) $.

$( A=carrier, B=default, C=src, D=dst2, E=k, F=l, G=q, H=i. $)
ntp4vc-tail-step-definition $a |- (
  NTP4VCTailStep A B C D E F G H
) <->
(
  (
    0 <_ ( ( G * ( E * F ) ) + H )
    /\
    ( ( G * ( E * F ) ) + H ) < ( # ` C )
  )
  /\
  (
    (
      0 <_ ( ( G * ( E * F ) ) + H )
      /\
      ( ( G * ( E * F ) ) + H ) < ( # ` D )
    )
    /\
    (
      (
        # `
        (
          NTP4VCSet
            D
            ( ( G * ( E * F ) ) + H )
            (
              NTP4VCAt
                C
                ( ( G * ( E * F ) ) + H )
                B
            )
        )
      )
      =
      ( # ` D )
      ->
      (
        (
          NTP4VCSetLaw
            D
            ( ( G * ( E * F ) ) + H )
            (
              NTP4VCAt
                C
                ( ( G * ( E * F ) ) + H )
                B
            )
            B
        )
        ->
        (
          NTP4VCTailInv
            C
            (
              NTP4VCSet
                D
                ( ( G * ( E * F ) ) + H )
                (
                  NTP4VCAt
                    C
                    ( ( G * ( E * F ) ) + H )
                    B
                )
            )
            E F G ( H + 1 ) B
        )
      )
    )
  )
) $.

$( A=carrier, B=default, C=src, D=original dst, E=old dst,
   F=k, G=l, H=q, I=r. $)
${
  $d i x A B C D E F G H I $.

  ntp4vc-tail-definition $a |- (
    NTP4VCTail A B C D E F G H I
  ) <->
  (
    (
      0 <_ ( ( I - 1 ) + 1 )
      ->
      (
        ( NTP4VCTailInv C E F G H 0 B )
        /\
        A. x e. Word A
          (
            ( # ` x ) = ( # ` E )
            ->
            (
              A. i e. ZZ
                (
                  (
                    (
                      0 <_ i
                      /\
                      i <_ ( I - 1 )
                    )
                    /\
                    (
                      NTP4VCTailInv
                        C x F G H i B
                    )
                  )
                  ->
                  (
                    NTP4VCTailStep
                      A B C x F G H i
                  )
                )
              /\
              (
                (
                  NTP4VCTailInv
                    C x F G H ( ( I - 1 ) + 1 ) B
                )
                ->
                (
                  NTP4VCCopy C x 0 ( # ` D ) B
                )
              )
            )
          )
      )
    )
    /\
    (
      ( ( I - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCCopy C E 0 ( # ` D ) B
      )
    )
  ) $.
$}

$( A=carrier, B=default, C=src, D=dst, E=k, F=l, G=q, H=r. $)
${
  $d s x A B C D E F G H $.

  ntp4vc-main-definition $a |- (
    NTP4VCMain A B C D E F G H
  ) <->
  (
    (
      0 <_ ( ( G - 1 ) + 1 )
      ->
      (
        ( NTP4VCCopy C D 0 ( 0 * ( E * F ) ) B )
        /\
        A. x e. Word A
          (
            ( # ` x ) = ( # ` D )
            ->
            (
              A. s e. ZZ
                (
                  (
                    (
                      0 <_ s
                      /\
                      s <_ ( G - 1 )
                    )
                    /\
                    (
                      NTP4VCCopy
                        C x 0 ( s * ( E * F ) ) B
                    )
                  )
                  ->
                  (
                    NTP4VCOuterStep
                      A B C x E F s
                  )
                )
              /\
              (
                (
                  NTP4VCCopy
                    C
                    x
                    0
                    ( ( ( G - 1 ) + 1 ) * ( E * F ) )
                    B
                )
                ->
                (
                  NTP4VCTail
                    A B C D x E F G H
                )
              )
            )
          )
      )
    )
    /\
    (
      ( ( G - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCTail
          A B C D D E F G H
      )
    )
  ) $.
$}

${
  $d A B C D E F G H $.

  $( The arbitrary inhabited source element type and theorem parameters. $)
  ntp4vc-elt-carrier-set $e |- A e. _V $.
  ntp4vc-elt-default $e |- B e. A $.
  ntp4vc-src-word $e |- C e. Word A $.
  ntp4vc-dst-word $e |- D e. Word A $.
  ntp4vc-k-integer $e |- E e. ZZ $.
  ntp4vc-l-integer $e |- F e. ZZ $.
  ntp4vc-q-integer $e |- G e. ZZ $.
  ntp4vc-r-integer $e |- H e. ZZ $.

  $( The eight source assumptions fact0 through fact7. $)
  ntp4vc-same-length $e |- ( # ` C ) = ( # ` D ) $.
  ntp4vc-positive-length $e |- 0 < ( # ` D ) $.
  ntp4vc-positive-k $e |- 0 < E $.
  ntp4vc-positive-l $e |- 0 < F $.
  ntp4vc-nonnegative-q $e |- 0 <_ G $.
  ntp4vc-nonnegative-r $e |- 0 <_ H $.
  ntp4vc-r-below-block $e |- H < ( E * F ) $.
  ntp4vc-length-decomposition $e |- (
    # ` D
  ) = ( ( ( G * E ) * F ) + H ) $.

  ntp4vc-pearl-verifythis-2024-smart-array-copy-0-vc $a |- (
    NTP4VCMain A B C D E F G H
  ) $.
$}
