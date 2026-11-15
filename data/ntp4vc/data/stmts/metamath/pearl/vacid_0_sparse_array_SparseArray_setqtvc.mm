$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vacid_0_sparse_array_SparseArray_setqtvc: the sparse-array set
  verification condition preserves the representation invariant while
  updating the value array and, when necessary, the index and back arrays,
  and establishes the pointwise value postcondition. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source element carrier. SetMM's ZZ is the
  full unbounded integer domain, and Word U and Word ZZ are exactly arbitrary
  finite zero-based source sequences; U itself is not restricted to a finite
  carrier.

  NTP4VCToNat reproduces Int.toNat, NTP4VCAt is integer-indexed lookup with
  the supplied default outside [0, length), and NTP4VCSet, NTP4VCNth, and
  NTP4VCFunUpdate reproduce List.set, integer-indexed lookup, and
  Function.update. NTP4VCInvariant is the complete Why3 sparse-array record
  invariant. NTP4VCValid adds the record's default field and all field types.
  NTP4VCIsElt, NTP4VCValue, and NTP4VCPost are direct expansions of the
  source definitions and postcondition.

  Sparse-array records are represented by their five fields under
  NTP4VCValid. This is bidirectionally equivalent to the source record type:
  every source record yields one valid field tuple, and every valid tuple
  forms a source record. The universally quantified first and second states
  therefore range over exactly the source sparse arrays. The remaining
  predicates are biconditional factorizations of the generated nested update
  obligations, including both repeated length premises and every guarded
  insertion branch.

  The final declaration is Metamath's native unproved $a statement encoding.
  Every preceding $a is syntax or a faithful definition needed to state it,
  and this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCNth NTP4VCFunUpdate
  NTP4VCSetLaw NTP4VCInvariant NTP4VCValid NTP4VCIsElt
  NTP4VCValue NTP4VCPost NTP4VCSecondStates NTP4VCBackWrite
  NTP4VCIndexWrite NTP4VCAfterValueWrite NTP4VCFirstStates
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.
ntp4vc-nth-syntax
  $a class ( NTP4VCNth A B ) $.
ntp4vc-fun-update-syntax
  $a class ( NTP4VCFunUpdate A B C ) $.

ntp4vc-set-law-syntax
  $a wff ( NTP4VCSetLaw A B C D ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E ) $.
ntp4vc-valid-syntax
  $a wff ( NTP4VCValid A B C D E F ) $.
ntp4vc-is-elt-syntax
  $a wff ( NTP4VCIsElt A B C D ) $.
ntp4vc-value-syntax
  $a class ( NTP4VCValue A B C D E F G ) $.
ntp4vc-post-syntax
  $a wff ( NTP4VCPost A B C D E F G H I J K L M ) $.
ntp4vc-second-states-syntax
  $a wff ( NTP4VCSecondStates A B C D E F G H I J K L M N ) $.
ntp4vc-back-write-syntax
  $a wff ( NTP4VCBackWrite A B C D E F G H I J K L M N ) $.
ntp4vc-index-write-syntax
  $a wff ( NTP4VCIndexWrite A B C D E F G H I J K L M N ) $.
ntp4vc-after-value-write-syntax
  $a wff ( NTP4VCAfterValueWrite A B C D E F G H I J K L M N ) $.
ntp4vc-first-states-syntax
  $a wff ( NTP4VCFirstStates A B C D E F G H I ) $.

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
  ( 0 <_ B /\ B < ( # ` A ) ) ,
  ( A ` B ) ,
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
  $d k A B $.

  ntp4vc-nth-definition $a |- (
    NTP4VCNth A B
  ) = (
    k e. ZZ |->
      ( NTP4VCAt A k B )
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

ntp4vc-set-law-definition $a |- (
  NTP4VCSetLaw A B C D
) <->
(
  ( NTP4VCNth ( NTP4VCSet A B C ) D )
  =
  (
    NTP4VCFunUpdate
      ( NTP4VCNth A D )
      B
      C
  )
) $.

${
  $d j A B C D E $.

  $( A=carrier, B=values, C=index, D=back, E=card. $)
  ntp4vc-invariant-definition $a |- (
    NTP4VCInvariant A B C D E
  ) <->
  (
    A e. _V
    /\
    (
      B e. Word A
      /\
      (
        C e. Word ZZ
        /\
        (
          D e. Word ZZ
          /\
          (
            E e. ZZ
            /\
            (
              0 <_ E
              /\
              (
                E <_ ( # ` B )
                /\
                (
                  ( # ` B ) <_ ; ; ; 1 0 0 0
                  /\
                  (
                    ( # ` B ) = ( # ` C )
                    /\
                    (
                      ( # ` C ) = ( # ` D )
                      /\
                      A. j e. ZZ
                        (
                          (
                            0 <_ j
                            /\
                            j < E
                          )
                          ->
                          (
                            (
                              0 <_ ( NTP4VCAt D j 0 )
                              /\
                              ( NTP4VCAt D j 0 ) < ( # ` B )
                            )
                            /\
                            (
                              NTP4VCAt
                                C
                                ( NTP4VCAt D j 0 )
                                0
                            ) = j
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

ntp4vc-valid-definition $a |- (
  NTP4VCValid A B C D E F
) <->
(
  ( NTP4VCInvariant A B C D E )
  /\
  F e. A
) $.

ntp4vc-is-elt-definition $a |- (
  NTP4VCIsElt A B C D
) <->
(
  (
    0 <_ ( NTP4VCAt A D 0 )
    /\
    ( NTP4VCAt A D 0 ) < C
  )
  /\
  (
    NTP4VCAt
      B
      ( NTP4VCAt A D 0 )
      0
  ) = D
) $.

ntp4vc-value-definition $a |- (
  NTP4VCValue A B C D E F G
) = if (
  ( NTP4VCIsElt B C D G ) ,
  ( NTP4VCAt A G F ) ,
  E
) $.

${
  $d j A B C D E F G H I J K L M $.

  $(
    A--E are the original fields, F--J the updated fields, K the
    inhabitant, L the distinguished index, and M the assigned value.
  $)
  ntp4vc-post-definition $a |- (
    NTP4VCPost A B C D E F G H I J K L M
  ) <->
  (
    ( NTP4VCValue F G H I J K L ) = M
    /\
    A. j e. ZZ
      (
        -. j = L
        ->
        (
          NTP4VCValue F G H I J K j
        ) = (
          NTP4VCValue A B C D E K j
        )
      )
  ) $.
$}

${
  $d p q r s t A B C D E F G H I J K L M N $.

  $(
    A is the carrier; B--F are the original fields; G--K are the first
    state's fields; L is the inhabitant; M is the index; N is the value.
  $)
  ntp4vc-second-states-definition $a |- (
    NTP4VCSecondStates A B C D E F G H I J K L M N
  ) <->
  A. p e. Word A
    A. q e. Word ZZ
      A. r e. Word ZZ
        A. s e. ZZ
          A. t e. A
            (
              ( NTP4VCValid A p q r s t )
              ->
              (
                (
                  NTP4VCInvariant
                    A
                    G
                    ( NTP4VCSet H M J )
                    ( NTP4VCSet I J M )
                    ( J + 1 )
                )
                /\
                (
                  (
                    K = t
                    /\
                    (
                      ( J + 1 ) = s
                      /\
                      (
                        ( NTP4VCSet I J M ) = r
                        /\
                        (
                          ( NTP4VCSet H M J ) = q
                          /\
                          G = p
                        )
                      )
                    )
                  )
                  ->
                  (
                    NTP4VCPost
                      B C D E F
                      p q r s t
                      L M N
                  )
                )
              )
            ) $.
$}

ntp4vc-back-write-definition $a |- (
  NTP4VCBackWrite A B C D E F G H I J K L M N
) <->
(
  (
    (
      #
      `
      ( NTP4VCSet I J M )
    ) = ( # ` I )
  )
  ->
  (
    (
      (
        #
        `
        ( NTP4VCSet I J M )
      ) = ( # ` I )
    )
    ->
    (
      ( NTP4VCSetLaw I J M 0 )
      ->
      (
        NTP4VCSecondStates
          A B C D E F
          G H I J K
          L M N
      )
    )
  )
) $.

ntp4vc-index-write-definition $a |- (
  NTP4VCIndexWrite A B C D E F G H I J K L M N
) <->
(
  (
    (
      #
      `
      ( NTP4VCSet H M J )
    ) = ( # ` H )
  )
  ->
  (
    (
      (
        #
        `
        ( NTP4VCSet H M J )
      ) = ( # ` H )
    )
    ->
    (
      ( NTP4VCSetLaw H M J 0 )
      ->
      (
        (
          0 <_ J
          /\
          J < ( # ` I )
        )
        /\
        (
          NTP4VCBackWrite
            A B C D E F
            G H I J K
            L M N
        )
      )
    )
  )
) $.

ntp4vc-after-value-write-definition $a |- (
  NTP4VCAfterValueWrite A B C D E F G H I J K L M N
) <->
(
  (
    0 <_ M
    /\
    M < ( # ` G )
  )
  /\
  (
    (
      -. ( NTP4VCIsElt H I J M )
      ->
      (
        (
          0 <_ M
          /\
          M < ( # ` H )
        )
        /\
        (
          NTP4VCIndexWrite
            A B C D E F
            G H I J K
            L M N
        )
      )
    )
    /\
    (
      ( NTP4VCIsElt H I J M )
      ->
      (
        NTP4VCPost
          B C D E F
          G H I J K
          L M N
      )
    )
  )
) $.

${
  $d p q r s t A B C D E F G H I $.

  $(
    A is the carrier; B--F are the original fields; G is the inhabitant;
    H is the index; I is the assigned value.
  $)
  ntp4vc-first-states-definition $a |- (
    NTP4VCFirstStates A B C D E F G H I
  ) <->
  A. p e. Word A
    A. q e. Word ZZ
      A. r e. Word ZZ
        A. s e. ZZ
          A. t e. A
            (
              ( NTP4VCValid A p q r s t )
              ->
              (
                (
                  ( # ` ( NTP4VCSet B H I ) )
                  =
                  ( # ` B )
                )
                ->
                (
                  (
                    ( # ` ( NTP4VCSet B H I ) )
                    =
                    ( # ` B )
                  )
                  ->
                  (
                    ( NTP4VCSetLaw B H I G )
                    ->
                    (
                      (
                        NTP4VCInvariant
                          A
                          ( NTP4VCSet B H I )
                          C
                          D
                          E
                      )
                      /\
                      (
                        (
                          F = t
                          /\
                          (
                            E = s
                            /\
                            (
                              D = r
                              /\
                              (
                                C = q
                                /\
                                ( NTP4VCSet B H I ) = p
                              )
                            )
                          )
                        )
                        ->
                        (
                          NTP4VCAfterValueWrite
                            A B C D E F
                            p q r s t
                            G H I
                        )
                      )
                    )
                  )
                )
              )
            ) $.
$}

${
  $d i v A B C D E F U $.

  $( F is the source Inhabited witness for U. $)
  ntp4vc-element-inhabitant $e |- F e. U $.

  $( A--E are the five fields of the original sparse-array parameter. $)
  ntp4vc-original-sparse-array $e |- (
    NTP4VCValid U A B C D E
  ) $.

  ntp4vc-index-integer $e |- i e. ZZ $.
  ntp4vc-value-in-carrier $e |- v e. U $.
  ntp4vc-fact0 $e |- 0 <_ i $.
  ntp4vc-fact1 $e |- i < ( # ` A ) $.

  ntp4vc-pearl-vacid-0-sparse-array-set-vc $a |- (
    0 <_ i
    /\
    (
      i < ( # ` A )
      /\
      (
        NTP4VCFirstStates
          U A B C D E F i v
      )
    )
  ) $.
$}
