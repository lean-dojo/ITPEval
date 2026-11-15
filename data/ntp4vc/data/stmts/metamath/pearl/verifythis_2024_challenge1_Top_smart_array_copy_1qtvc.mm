$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2024_challenge1_Top_smart_array_copy_1qtvc: the Smart
  Array Copy 1 verification condition maintains mutually inverse index
  permutations while copying shuffled fixed-size subsegments and a final
  remainder segment. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary inhabited element type is represented by a SetMM carrier A
  with a selected element B, and source arrays are arbitrary finite words
  over A. Integer arrays are arbitrary finite words over ZZ. NTP4VCToNat,
  NTP4VCAt, NTP4VCSet, and NTP4VCSetLaw reproduce the exported Int.toNat,
  totalized list lookup, List.set, and integer-keyed functional-update
  premise. NTP4VCIdentity is the unique zero-based identity word specified by
  the source identity function.

  The remaining biconditional definitions directly factor the source
  permutation, copy, frame, nested outer/subsegment/element loop, and tail
  obligations. Expanding them recovers every word and integer quantifier,
  length premise, guarded update, invariant, implication, and final
  copy_perm conclusion in the official Why3 verification condition and its
  agreeing Lean, Rocq, and Isabelle exports. The final $a declaration is
  Metamath's native unproved statement encoding; there is no $p declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCSetLaw NTP4VCIdentity
  NTP4VCIdentitySpec NTP4VCValidChunk NTP4VCCopyTo NTP4VCFrame
  NTP4VCPermutation NTP4VCPermutationPair NTP4VCCopyPerm
  NTP4VCStartSrc NTP4VCStartDst NTP4VCCopySubsegment
  NTP4VCJInvariant NTP4VCIInvariant NTP4VCIUpdate
  NTP4VCILoop NTP4VCJStep NTP4VCJLoop NTP4VCOuterStep
  NTP4VCTailStep NTP4VCTail NTP4VCOuterLoop NTP4VCMain
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.
ntp4vc-identity-syntax
  $a class ( NTP4VCIdentity A ) $.
ntp4vc-start-src-syntax
  $a class ( NTP4VCStartSrc A B C D E ) $.
ntp4vc-start-dst-syntax
  $a class ( NTP4VCStartDst A B C D E F ) $.

ntp4vc-set-law-syntax
  $a wff ( NTP4VCSetLaw A B C D ) $.
ntp4vc-identity-spec-syntax
  $a wff ( NTP4VCIdentitySpec A B ) $.
ntp4vc-valid-chunk-syntax
  $a wff ( NTP4VCValidChunk A B C ) $.
ntp4vc-copy-to-syntax
  $a wff ( NTP4VCCopyTo A B C D E F ) $.
ntp4vc-frame-syntax
  $a wff ( NTP4VCFrame A B C D E ) $.
ntp4vc-permutation-syntax
  $a wff ( NTP4VCPermutation A B ) $.
ntp4vc-permutation-pair-syntax
  $a wff ( NTP4VCPermutationPair A B C ) $.
ntp4vc-copy-perm-syntax
  $a wff ( NTP4VCCopyPerm A B C D E F ) $.
ntp4vc-copy-subsegment-syntax
  $a wff ( NTP4VCCopySubsegment A B C D E F G H I J K ) $.
ntp4vc-j-invariant-syntax
  $a wff ( NTP4VCJInvariant A B C D E F G H I J K ) $.
ntp4vc-i-invariant-syntax
  $a wff ( NTP4VCIInvariant A B C D E F G H I J K L M N O ) $.
ntp4vc-i-update-syntax
  $a wff ( NTP4VCIUpdate A B C D E F G H I J K L M N O ) $.
ntp4vc-i-loop-syntax
  $a wff ( NTP4VCILoop A B C D E F G H I J K L ) $.
ntp4vc-j-step-syntax
  $a wff ( NTP4VCJStep A B C D E F G H I J K L ) $.
ntp4vc-j-loop-syntax
  $a wff ( NTP4VCJLoop A B C D E F G H I J K ) $.
ntp4vc-outer-step-syntax
  $a wff ( NTP4VCOuterStep A B C D E F G H I ) $.
ntp4vc-tail-step-syntax
  $a wff ( NTP4VCTailStep A B C D E F G H I J ) $.
ntp4vc-tail-syntax
  $a wff ( NTP4VCTail A B C D E F G H I J K ) $.
ntp4vc-outer-loop-syntax
  $a wff ( NTP4VCOuterLoop A B C D E F G H I J ) $.
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
  $d x A B C D $.

  ntp4vc-set-law-definition $a |- (
    NTP4VCSetLaw A B C D
  ) <->
  A. x e. ZZ
    (
      ( NTP4VCAt ( NTP4VCSet A B C ) x D )
      =
      if (
        x = B ,
        C ,
        ( NTP4VCAt A x D )
      )
    ) $.
$}

${
  $d k A $.

  ntp4vc-identity-definition $a |- (
    NTP4VCIdentity A
  ) = (
    k e. ( 0 ..^ A ) |-> k
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
  $d i A B C D E F $.

  ntp4vc-copy-to-definition $a |- (
    NTP4VCCopyTo A B C D E F
  ) <->
  (
    ( NTP4VCValidChunk A C E )
    /\
    (
      ( NTP4VCValidChunk B D E )
      /\
      (
        ( # ` A ) = ( # ` B )
        /\
        (
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < E
              )
              ->
              (
                ( NTP4VCAt B ( D + i ) F )
                =
                ( NTP4VCAt A ( C + i ) F )
              )
            )
          /\
          A. i e. ZZ
            (
              (
                D <_ i
                /\
                i < ( D + E )
              )
              ->
              (
                ( NTP4VCAt B i F )
                =
                ( NTP4VCAt A ( i + ( C - D ) ) F )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-frame-definition $a |- (
    NTP4VCFrame A B C D E
  ) <->
  (
    ( # ` B ) = ( # ` A )
    /\
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < C
          )
          ->
          (
            ( NTP4VCAt B i E )
            =
            ( NTP4VCAt A i E )
          )
        )
      /\
      A. i e. ZZ
        (
          (
            ( C + D ) <_ i
            /\
            i < ( # ` B )
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
              NTP4VCAt B ( NTP4VCAt C i 0 ) 0
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
              NTP4VCAt C ( NTP4VCAt B i 0 ) 0
            )
            =
            i
          )
      )
    )
  ) $.
$}

${
  $d i A B C D E F $.

  ntp4vc-copy-perm-definition $a |- (
    NTP4VCCopyPerm A B C D E F
  ) <->
  (
    ( NTP4VCValidChunk A 0 C )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      (
        ( NTP4VCPermutationPair C D E )
        /\
        (
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < C
              )
              ->
              (
                0 <_ ( NTP4VCAt D i 0 )
                /\
                ( NTP4VCAt D i 0 ) < C
              )
            )
          /\
          (
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i < C
                )
                ->
                (
                  0 <_ ( NTP4VCAt E i 0 )
                  /\
                  ( NTP4VCAt E i 0 ) < C
                )
              )
            /\
            (
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < C
                  )
                  ->
                  (
                    ( NTP4VCAt B i F )
                    =
                    ( NTP4VCAt A ( NTP4VCAt D i 0 ) F )
                  )
                )
              /\
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < C
                  )
                  ->
                  (
                    ( NTP4VCAt A i F )
                    =
                    ( NTP4VCAt B ( NTP4VCAt E i 0 ) F )
                  )
                )
            )
          )
        )
      )
    )
  ) $.
$}

ntp4vc-identity-spec-definition $a |- (
  NTP4VCIdentitySpec A B
) <->
(
  ( # ` A ) = B
  /\
  (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        ( NTP4VCAt A i 0 ) = i
      )
    /\
    ( NTP4VCPermutationPair B A A )
  )
) $.

ntp4vc-start-src-definition $a |- (
  NTP4VCStartSrc A B C D E
) = (
  ( A * ( B * C ) )
  +
  ( ( NTP4VCAt E D 0 ) * B )
) $.

ntp4vc-start-dst-definition $a |- (
  NTP4VCStartDst A B C D E F
) = (
  ( A * ( B * C ) )
  +
  (
    (
      NTP4VCAt F ( NTP4VCAt E D 0 ) 0
    )
    *
    B
  )
) $.

${
  $d i A B C D E F G H I J K $.

  $( A=src, B=dst, C=s, D=k, E=l, F=j,
     G=sigma, H=tau, I=p, J=invp, K=default. $)
  ntp4vc-copy-subsegment-definition $a |- (
    NTP4VCCopySubsegment A B C D E F G H I J K
  ) <->
  (
    (
      NTP4VCCopyTo
        A B
        ( NTP4VCStartSrc C D E F G )
        ( NTP4VCStartDst C D E F G H )
        D K
    )
    /\
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < D
          )
          ->
          (
            NTP4VCAt
              I
              ( ( NTP4VCStartDst C D E F G H ) + i )
              0
          )
          =
          ( ( NTP4VCStartSrc C D E F G ) + i )
        )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < D
          )
          ->
          (
            NTP4VCAt
              J
              ( ( NTP4VCStartSrc C D E F G ) + i )
              0
          )
          =
          ( ( NTP4VCStartDst C D E F G H ) + i )
        )
    )
  ) $.
$}

${
  $d j A B C D E F G H I J K $.

  $( A=src, B=dst, C=p, D=invp, E=s, F=k, G=l,
     H=j, I=sigma, J=tau, K=default. $)
  ntp4vc-j-invariant-definition $a |- (
    NTP4VCJInvariant A B C D E F G H I J K
  ) <->
  (
    ( NTP4VCPermutationPair ( E * ( F * G ) ) C D )
    /\
    (
      ( NTP4VCCopyPerm A B ( E * ( F * G ) ) C D K )
      /\
      A. j e. ZZ
        (
          (
            0 <_ j
            /\
            j < H
          )
          ->
          (
            NTP4VCCopySubsegment
              A B E F G j I J C D K
          )
        )
    )
  ) $.
$}

${
  $d i j A B C D E F G H I J K L M N O $.

  $( A=src, B=base dst, C=base p, D=base invp,
     E=current dst, F=current p, G=current invp, H=s, I=k, J=l,
     K=j, L=sigma, M=tau, N=i, O=default. $)
  ntp4vc-i-invariant-definition $a |- (
    NTP4VCIInvariant A B C D E F G H I J K L M N O
  ) <->
  (
    (
      NTP4VCFrame
        B E
        ( NTP4VCStartDst H I J K L M )
        I O
    )
    /\
    (
      (
        NTP4VCFrame
          C F
          ( NTP4VCStartDst H I J K L M )
          I 0
      )
      /\
      (
        (
          NTP4VCFrame
            D G
            ( NTP4VCStartSrc H I J K L )
            I 0
        )
        /\
        (
          ( NTP4VCPermutationPair ( H * ( I * J ) ) F G )
          /\
          (
            ( NTP4VCCopyPerm A E ( H * ( I * J ) ) F G O )
            /\
            (
              (
                NTP4VCCopyTo
                  A E
                  ( NTP4VCStartSrc H I J K L )
                  ( NTP4VCStartDst H I J K L M )
                  N O
              )
              /\
              (
                A. i e. ZZ
                  (
                    (
                      0 <_ i
                      /\
                      i < N
                    )
                    ->
                    (
                      NTP4VCAt
                        F
                        ( ( NTP4VCStartDst H I J K L M ) + i )
                        0
                    )
                    =
                    ( ( NTP4VCStartSrc H I J K L ) + i )
                  )
                /\
                (
                  A. i e. ZZ
                    (
                      (
                        0 <_ i
                        /\
                        i < N
                      )
                      ->
                      (
                        NTP4VCAt
                          G
                          ( ( NTP4VCStartSrc H I J K L ) + i )
                          0
                      )
                      =
                      ( ( NTP4VCStartDst H I J K L M ) + i )
                    )
                  /\
                  A. j e. ZZ
                    (
                      (
                        0 <_ j
                        /\
                        j < K
                      )
                      ->
                      (
                        NTP4VCCopySubsegment
                          A E H I J j L M F G O
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

$( The element-loop body performs the three sequential word updates. $)
ntp4vc-i-update-definition $a |- (
  NTP4VCIUpdate A B C D E F G H I J K L M N O
) <->
(
  (
    0 <_ ( ( NTP4VCStartSrc H I J K L ) + N )
    /\
    ( ( NTP4VCStartSrc H I J K L ) + N ) < ( # ` A )
  )
  /\
  (
    (
      0 <_ ( ( NTP4VCStartDst H I J K L M ) + N )
      /\
      ( ( NTP4VCStartDst H I J K L M ) + N ) < ( # ` E )
    )
    /\
    (
      (
        ( # `
          ( NTP4VCSet
              E
              ( ( NTP4VCStartDst H I J K L M ) + N )
              ( NTP4VCAt
                  A
                  ( ( NTP4VCStartSrc H I J K L ) + N )
                  O
              )
          )
        )
        =
        ( # ` E )
      )
      ->
      (
        (
          NTP4VCSetLaw
            E
            ( ( NTP4VCStartDst H I J K L M ) + N )
            ( NTP4VCAt
                A
                ( ( NTP4VCStartSrc H I J K L ) + N )
                O
            )
            O
        )
        ->
        (
          (
            0 <_ ( ( NTP4VCStartDst H I J K L M ) + N )
            /\
            ( ( NTP4VCStartDst H I J K L M ) + N ) < ( # ` F )
          )
          /\
          (
            (
              ( # `
                ( NTP4VCSet
                    F
                    ( ( NTP4VCStartDst H I J K L M ) + N )
                    ( ( NTP4VCStartSrc H I J K L ) + N )
                )
              )
              =
              ( # ` F )
            )
            ->
            (
              (
                NTP4VCSetLaw
                  F
                  ( ( NTP4VCStartDst H I J K L M ) + N )
                  ( ( NTP4VCStartSrc H I J K L ) + N )
                  0
              )
              ->
              (
                (
                  0 <_ ( ( NTP4VCStartSrc H I J K L ) + N )
                  /\
                  ( ( NTP4VCStartSrc H I J K L ) + N ) < ( # ` G )
                )
                /\
                (
                  (
                    ( # `
                      ( NTP4VCSet
                          G
                          ( ( NTP4VCStartSrc H I J K L ) + N )
                          ( ( NTP4VCStartDst H I J K L M ) + N )
                      )
                    )
                    =
                    ( # ` G )
                  )
                  ->
                  (
                    (
                      NTP4VCSetLaw
                        G
                        ( ( NTP4VCStartSrc H I J K L ) + N )
                        ( ( NTP4VCStartDst H I J K L M ) + N )
                        0
                    )
                    ->
                    (
                      NTP4VCIInvariant
                        A B C D
                        ( NTP4VCSet
                            E
                            ( ( NTP4VCStartDst H I J K L M ) + N )
                            ( NTP4VCAt
                                A
                                ( ( NTP4VCStartSrc H I J K L ) + N )
                                O
                            )
                        )
                        ( NTP4VCSet
                            F
                            ( ( NTP4VCStartDst H I J K L M ) + N )
                            ( ( NTP4VCStartSrc H I J K L ) + N )
                        )
                        ( NTP4VCSet
                            G
                            ( ( NTP4VCStartSrc H I J K L ) + N )
                            ( ( NTP4VCStartDst H I J K L M ) + N )
                        )
                        H I J K L M ( N + 1 ) O
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

${
  $d i d p u A B C D E F G H I J K L $.

  $( A=src, B=dst2, C=p2, D=invp2, E=s, F=k, G=l,
     H=j, I=sigma, J=tau, K=default, L=carrier. $)
  ntp4vc-i-loop-definition $a |- (
    NTP4VCILoop A B C D E F G H I J K L
  ) <->
  (
    (
      0 <_ ( ( F - 1 ) + 1 )
      ->
      (
        (
          NTP4VCIInvariant
            A B C D B C D E F G H I J 0 K
        )
        /\
        A. u e. Word ZZ
          A. p e. Word ZZ
            A. d e. Word L
              (
                ( # ` u ) = ( # ` D )
                ->
                (
                  ( # ` p ) = ( # ` C )
                  ->
                  (
                    ( # ` d ) = ( # ` B )
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
                              NTP4VCIInvariant
                                A B C D d p u
                                E F G H I J i K
                            )
                          )
                          ->
                          (
                            NTP4VCIUpdate
                              A B C D d p u
                              E F G H I J i K
                          )
                        )
                      /\
                      (
                        (
                          NTP4VCIInvariant
                            A B C D d p u
                            E F G H I J ( ( F - 1 ) + 1 ) K
                        )
                        ->
                        (
                          NTP4VCJInvariant
                            A d p u E F G ( H + 1 ) I J K
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
      ( ( F - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCJInvariant
          A B C D E F G ( H + 1 ) I J K
      )
    )
  ) $.
$}

$( A=src, B=dst2, C=p2, D=invp2, E=s, F=k, G=l,
   H=j, I=sigma, J=tau, K=default, L=carrier. $)
ntp4vc-j-step-definition $a |- (
  NTP4VCJStep A B C D E F G H I J K L
) <->
(
  (
    0 <_ H
    /\
    H < ( # ` I )
  )
  /\
  (
    (
      0 <_ H
      /\
      H < ( # ` I )
    )
    /\
    (
      (
        0 <_ ( NTP4VCAt I H 0 )
        /\
        ( NTP4VCAt I H 0 ) < ( # ` J )
      )
      /\
      (
        NTP4VCILoop A B C D E F G H I J K L
      )
    )
  )
) $.

${
  $d j d p u A B C D E F G H I J K $.

  $( A=src, B=dst1, C=p1, D=invp1, E=s, F=k, G=l,
     H=sigma, I=tau, J=default, K=carrier. $)
  ntp4vc-j-loop-definition $a |- (
    NTP4VCJLoop A B C D E F G H I J K
  ) <->
  (
    (
      0 <_ ( ( G - 1 ) + 1 )
      ->
      (
        (
          NTP4VCJInvariant A B C D E F G 0 H I J
        )
        /\
        A. u e. Word ZZ
          A. p e. Word ZZ
            A. d e. Word K
              (
                ( # ` u ) = ( # ` D )
                ->
                (
                  ( # ` p ) = ( # ` C )
                  ->
                  (
                    ( # ` d ) = ( # ` B )
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
                              NTP4VCJInvariant
                                A d p u E F G j H I J
                            )
                          )
                          ->
                          (
                            NTP4VCJStep
                              A d p u E F G j H I J K
                          )
                        )
                      /\
                      (
                        (
                          NTP4VCJInvariant
                            A d p u E F G ( ( G - 1 ) + 1 ) H I J
                        )
                        ->
                        (
                          ( NTP4VCPermutationPair
                              ( ( E + 1 ) * ( F * G ) ) p u
                          )
                          /\
                          (
                            NTP4VCCopyPerm
                              A d
                              ( ( E + 1 ) * ( F * G ) )
                              p u J
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
      ( ( G - 1 ) + 1 ) < 0
      ->
      (
        ( NTP4VCPermutationPair
            ( ( E + 1 ) * ( F * G ) ) C D
        )
        /\
        (
          NTP4VCCopyPerm
            A B
            ( ( E + 1 ) * ( F * G ) )
            C D J
        )
      )
    )
  ) $.
$}

${
  $d a b c d A B C D E F G H I $.

  $( A=src, B=dst1, C=p1, D=invp1, E=s, F=k, G=l,
     H=default, I=carrier. $)
  ntp4vc-outer-step-definition $a |- (
    NTP4VCOuterStep A B C D E F G H I
  ) <->
  (
    0 < G
    /\
    A. a e. Word ZZ
      A. b e. Word ZZ
        (
          (
            (
              ( # ` a ) = ( # ` b )
              /\
              ( # ` b ) = G
            )
            /\
            ( NTP4VCPermutationPair G a b )
          )
          ->
          (
            0 < G
            /\
            A. c e. Word ZZ
              A. d e. Word ZZ
                (
                  (
                    (
                      ( # ` c ) = ( # ` d )
                      /\
                      ( # ` d ) = G
                    )
                    /\
                    ( NTP4VCPermutationPair G c d )
                  )
                  ->
                  (
                    NTP4VCJLoop
                      A B C D E F G a c H I
                  )
                )
          )
        )
  ) $.
$}

$( A=src, B=current dst, C=current p, D=current invp,
   E=last, F=i, G=default; H,I,J are unused padding. $)
ntp4vc-tail-step-definition $a |- (
  NTP4VCTailStep A B C D E F G H I J
) <->
(
  (
    0 <_ ( E + F )
    /\
    ( E + F ) < ( # ` A )
  )
  /\
  (
    (
      0 <_ ( E + F )
      /\
      ( E + F ) < ( # ` B )
    )
    /\
    (
      (
        ( # `
          ( NTP4VCSet
              B ( E + F ) ( NTP4VCAt A ( E + F ) G )
          )
        )
        =
        ( # ` B )
      )
      ->
      (
        (
          NTP4VCSetLaw
            B ( E + F ) ( NTP4VCAt A ( E + F ) G ) G
        )
        ->
        (
          (
            0 <_ ( E + F )
            /\
            ( E + F ) < ( # ` C )
          )
          /\
          (
            (
              ( # ` ( NTP4VCSet C ( E + F ) ( E + F ) ) )
              =
              ( # ` C )
            )
            ->
            (
              (
                NTP4VCSetLaw C ( E + F ) ( E + F ) 0
              )
              ->
              (
                (
                  0 <_ ( E + F )
                  /\
                  ( E + F ) < ( # ` D )
                )
                /\
                (
                  (
                    ( # ` ( NTP4VCSet D ( E + F ) ( E + F ) ) )
                    =
                    ( # ` D )
                  )
                  ->
                  (
                    (
                      NTP4VCSetLaw D ( E + F ) ( E + F ) 0
                    )
                    ->
                    (
                      (
                        NTP4VCPermutationPair
                          ( E + ( F + 1 ) )
                          ( NTP4VCSet C ( E + F ) ( E + F ) )
                          ( NTP4VCSet D ( E + F ) ( E + F ) )
                      )
                      /\
                      (
                        NTP4VCCopyPerm
                          A
                          ( NTP4VCSet
                              B ( E + F ) ( NTP4VCAt A ( E + F ) G )
                          )
                          ( E + ( F + 1 ) )
                          ( NTP4VCSet C ( E + F ) ( E + F ) )
                          ( NTP4VCSet D ( E + F ) ( E + F ) )
                          G
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

${
  $d i d p u A B C D E F G H I J K $.

  $( A=src, B=original dst, C=current dst, D=p, E=invp,
     F=k, G=l, H=q, I=r, J=default, K=carrier. $)
  ntp4vc-tail-definition $a |- (
    NTP4VCTail A B C D E F G H I J K
  ) <->
  (
    (
      0 <_ ( ( I - 1 ) + 1 )
      ->
      (
        (
          ( NTP4VCPermutationPair
              ( ( H * ( F * G ) ) + 0 ) D E
          )
          /\
          (
            NTP4VCCopyPerm
              A C ( ( H * ( F * G ) ) + 0 ) D E J
          )
        )
        /\
        A. u e. Word ZZ
          A. p e. Word ZZ
            A. d e. Word K
              (
                ( # ` u ) = ( # ` E )
                ->
                (
                  ( # ` p ) = ( # ` D )
                  ->
                  (
                    ( # ` d ) = ( # ` C )
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
                              ( NTP4VCPermutationPair
                                  ( ( H * ( F * G ) ) + i ) p u
                              )
                              /\
                              (
                                NTP4VCCopyPerm
                                  A d
                                  ( ( H * ( F * G ) ) + i )
                                  p u J
                              )
                            )
                          )
                          ->
                          (
                            NTP4VCTailStep
                              A d p u
                              ( H * ( F * G ) )
                              i J 0 0 0
                          )
                        )
                      /\
                      (
                        (
                          ( NTP4VCPermutationPair
                              (
                                ( H * ( F * G ) )
                                +
                                ( ( I - 1 ) + 1 )
                              )
                              p u
                          )
                          /\
                          (
                            NTP4VCCopyPerm
                              A d
                              (
                                ( H * ( F * G ) )
                                +
                                ( ( I - 1 ) + 1 )
                              )
                              p u J
                          )
                        )
                        ->
                        (
                          NTP4VCCopyPerm
                            A d ( # ` B ) p u J
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
      ( ( I - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCCopyPerm A C ( # ` B ) D E J
      )
    )
  ) $.
$}

${
  $d s d p u A B C D E F G H I J $.

  $( A=carrier, B=default, C=src, D=dst, E=p, F=invp,
     G=k, H=l, I=q, J=r. $)
  ntp4vc-outer-loop-definition $a |- (
    NTP4VCOuterLoop A B C D E F G H I J
  ) <->
  (
    (
      0 <_ ( ( I - 1 ) + 1 )
      ->
      (
        (
          ( NTP4VCPermutationPair ( 0 * ( G * H ) ) E F )
          /\
          (
            NTP4VCCopyPerm C D ( 0 * ( G * H ) ) E F B
          )
        )
        /\
        A. u e. Word ZZ
          A. p e. Word ZZ
            A. d e. Word A
              (
                ( # ` u ) = ( # ` F )
                ->
                (
                  ( # ` p ) = ( # ` E )
                  ->
                  (
                    ( # ` d ) = ( # ` D )
                    ->
                    (
                      A. s e. ZZ
                        (
                          (
                            (
                              0 <_ s
                              /\
                              s <_ ( I - 1 )
                            )
                            /\
                            (
                              ( NTP4VCPermutationPair
                                  ( s * ( G * H ) ) p u
                              )
                              /\
                              (
                                NTP4VCCopyPerm
                                  C d ( s * ( G * H ) ) p u B
                              )
                            )
                          )
                          ->
                          (
                            NTP4VCOuterStep
                              C d p u s G H B A
                          )
                        )
                      /\
                      (
                        (
                          ( NTP4VCPermutationPair
                              ( ( ( I - 1 ) + 1 ) * ( G * H ) )
                              p u
                          )
                          /\
                          (
                            NTP4VCCopyPerm
                              C d
                              ( ( ( I - 1 ) + 1 ) * ( G * H ) )
                              p u B
                          )
                        )
                        ->
                        (
                          NTP4VCTail
                            C D d p u G H I J B A
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
      ( ( I - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCTail
          C D D E F G H I J B A
      )
    )
  ) $.
$}

ntp4vc-main-definition $a |- (
  NTP4VCMain A B C D E F G H
) <->
(
  0 < ( # ` D )
  /\
  (
    (
      NTP4VCIdentitySpec
        ( NTP4VCIdentity ( # ` D ) )
        ( # ` D )
    )
    ->
    (
      0 < ( # ` D )
      /\
      (
        (
          NTP4VCIdentitySpec
            ( NTP4VCIdentity ( # ` D ) )
            ( # ` D )
        )
        ->
        (
          NTP4VCOuterLoop
            A B C D
            ( NTP4VCIdentity ( # ` D ) )
            ( NTP4VCIdentity ( # ` D ) )
            E F G H
        )
      )
    )
  )
) $.

${
  $d
    a b c d i j k p s u x
    A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
  $.

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

  ntp4vc-pearl-verifythis-2024-smart-array-copy-1-vc $a |- (
    NTP4VCMain A B C D E F G H
  ) $.
$}
