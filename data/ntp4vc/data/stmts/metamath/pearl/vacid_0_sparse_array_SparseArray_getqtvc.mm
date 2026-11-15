$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vacid_0_sparse_array_SparseArray_getqtvc: the sparse-array get
  verification condition preserves the requested index bounds and states
  that either lookup branch returns the abstract sparse-array value. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary source element carrier, F is its chosen inhabitant, and
  A, B, C, D, E are respectively the values word, index word, back word,
  cardinality, and default field of the sparse-array record. SetMM words are
  exactly arbitrary finite zero-based sequences; U itself is not restricted
  to a finite carrier. ZZ is the full unbounded integer domain.

  NTP4VCToNat and NTP4VCAt reproduce Int.toNat and totalized list lookup.
  NTP4VCValid is the complete Why3 sparse-array record invariant, including
  all three word types, the cardinality and length bounds, equal lengths, and
  the universally quantified index/back consistency condition.
  NTP4VCIsElt, NTP4VCValue, and NTP4VCResult are direct expansions of
  is_elt, value, and the proposition-valued conditional that specifies the
  result of get.

  Representing the record by its five fields under NTP4VCValid is
  bidirectionally equivalent to the source record type: every source record
  yields exactly these fields, and every such field tuple is a source record.
  No sparse-array equality occurs in this VC, so record extensionality adds no
  further premise. The final declaration is Metamath's native unproved $a
  statement encoding; every preceding $a is syntax or a faithful definition
  needed to state it, and this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCValid
  NTP4VCIsElt NTP4VCValue NTP4VCResult
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B C ) $.
ntp4vc-valid-syntax
  $a wff ( NTP4VCValid A B C D E F ) $.
ntp4vc-is-elt-syntax
  $a wff ( NTP4VCIsElt A B C D ) $.
ntp4vc-value-syntax
  $a class ( NTP4VCValue A B C D E F G ) $.
ntp4vc-result-syntax
  $a wff ( NTP4VCResult A B C D E F G H ) $.

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
  $d j A B C D E F $.

  $(
    A=element carrier, B=values, C=index, D=back, E=card, F=default.
  $)
  ntp4vc-valid-definition $a |- (
    NTP4VCValid A B C D E F
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
              F e. A
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
    )
  ) $.
$}

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

ntp4vc-result-definition $a |- (
  NTP4VCResult A B C D E F G H
) <->
(
  (
    ( NTP4VCIsElt B C D G )
    /\
    H = ( NTP4VCAt A G F )
  )
  \/
  (
    -. ( NTP4VCIsElt B C D G )
    /\
    H = E
  )
) $.

${
  $d i j r A B C D E F U $.

  $( F is the source Inhabited witness for U. $)
  ntp4vc-element-inhabitant $e |- F e. U $.

  $(
    A, B, C, D, E are the fields of the source sparse-array parameter a.
  $)
  ntp4vc-sparse-array $e |- (
    NTP4VCValid U A B C D E
  ) $.

  ntp4vc-index-integer $e |- i e. ZZ $.
  ntp4vc-fact0 $e |- 0 <_ i $.
  ntp4vc-fact1 $e |- i < ( # ` A ) $.

  ntp4vc-pearl-vacid-0-sparse-array-get-vc $a |- (
    0 <_ i
    /\
    (
      i < ( # ` A )
      /\
      (
        (
          ( NTP4VCIsElt B C D i )
          ->
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
        )
        /\
        A. r e. U
          (
            (
              NTP4VCResult A B C D E F i r
            )
            ->
            r = (
              NTP4VCValue A B C D E F i
            )
          )
      )
    )
  ) $.
$}
