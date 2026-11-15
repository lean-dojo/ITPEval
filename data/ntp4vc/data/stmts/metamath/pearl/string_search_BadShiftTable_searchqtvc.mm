$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/string_search_BadShiftTable_searchqtvc: the bad-character-shift
  string-search verification condition preserves the no-earlier-match
  invariant, signed 63-bit bounds and progress, and the success-or-absence
  result specification. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCByte is the complete 8-bit character carrier, and NTP4VCBV63 is
  the complete signed-value image of 63-bit words. Signed value is a
  bijection from source words to this integer interval, so representing a
  word by its signed integer preserves both word equality and every signed
  arithmetic comparison in the verification condition. SetMM words over
  NTP4VCByte are exactly arbitrary finite source strings.

  NTP4VCFMap is the full carrier of finite partial functions from bytes to
  signed 63-bit values. The source implementation carrier t int63 remains an
  arbitrary inhabited set, with an arbitrary total to_fmap projection into
  NTP4VCFMap. The bad-shift-table record also remains an arbitrary inhabited
  carrier with total pattern and table projections, record extensionality,
  and its complete invariant law.

  NTP4VCToNat and NTP4VCAt reproduce source integer-to-natural conversion
  and totalized string lookup. NTP4VCSubstring uses SetMM's subword operator
  with endpoint start + count, exactly rendering the authoritative Why3
  substring text start count operation. The record invariant and all
  continuation predicates are biconditional factorizations. Expanding them
  recovers every source domain, assumption, quantifier, signed bound,
  implication, conditional branch, loop invariant, variant-decrease
  obligation, and final postcondition. The final $a declaration is
  Metamath's native unproved statement encoding; every preceding $a is syntax
  or a faithful definition required to state it, and this database contains
  no $p proof declaration.
$)

$c
  NTP4VCByte NTP4VCIn63 NTP4VCBV63 NTP4VCFMap
  NTP4VCToNat NTP4VCAt NTP4VCSubstring
  NTP4VCPrefixPresent NTP4VCShiftBounds NTP4VCFinalNoOccurrence
  NTP4VCBadShiftInvariant NTP4VCMatches NTP4VCNoMatchBefore
  NTP4VCSearchInvariant NTP4VCSearchPost
  NTP4VCShiftAvailability NTP4VCShiftValue NTP4VCAfterShift
  NTP4VCReadCharacter NTP4VCAdvance NTP4VCAfterFailed
  NTP4VCGuardTrue NTP4VCIteration NTP4VCSearchBody NTP4VCSearchVC
$.

ntp4vcss-byte-syntax $a class NTP4VCByte $.
ntp4vcss-in63-syntax $a wff ( NTP4VCIn63 A ) $.
ntp4vcss-bv63-syntax $a class NTP4VCBV63 $.
ntp4vcss-fmap-syntax $a class NTP4VCFMap $.
ntp4vcss-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vcss-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vcss-substring-syntax
  $a class ( NTP4VCSubstring A B C ) $.

ntp4vcss-prefix-present-syntax
  $a wff ( NTP4VCPrefixPresent A B C ) $.
ntp4vcss-shift-bounds-syntax
  $a wff ( NTP4VCShiftBounds A B ) $.
ntp4vcss-final-no-occurrence-syntax
  $a wff ( NTP4VCFinalNoOccurrence A B ) $.
ntp4vcss-bad-shift-invariant-syntax
  $a wff ( NTP4VCBadShiftInvariant A B ) $.
ntp4vcss-matches-syntax
  $a wff ( NTP4VCMatches A B C ) $.
ntp4vcss-no-match-before-syntax
  $a wff ( NTP4VCNoMatchBefore A B C D E ) $.
ntp4vcss-search-invariant-syntax
  $a wff ( NTP4VCSearchInvariant A B C D E ) $.
ntp4vcss-search-post-syntax
  $a wff ( NTP4VCSearchPost A B C ) $.
ntp4vcss-shift-availability-syntax
  $a wff ( NTP4VCShiftAvailability A B C ) $.
ntp4vcss-shift-value-syntax
  $a wff ( NTP4VCShiftValue A B C D ) $.
ntp4vcss-after-shift-syntax
  $a wff ( NTP4VCAfterShift A B C D E F ) $.
ntp4vcss-read-character-syntax
  $a wff ( NTP4VCReadCharacter A B C D E F G ) $.
ntp4vcss-advance-syntax
  $a wff ( NTP4VCAdvance A B C D E F ) $.
ntp4vcss-after-failed-syntax
  $a wff ( NTP4VCAfterFailed A B C D E F ) $.
ntp4vcss-guard-true-syntax
  $a wff ( NTP4VCGuardTrue A B C D E F ) $.
ntp4vcss-iteration-syntax
  $a wff ( NTP4VCIteration A B C D E F ) $.
ntp4vcss-search-body-syntax
  $a wff ( NTP4VCSearchBody A B C D E ) $.
ntp4vcss-search-vc-syntax
  $a wff ( NTP4VCSearchVC A B C ) $.

ntp4vcss-byte-definition $a |- NTP4VCByte =
  ( 0 ... ( ( 2 ^ 8 ) - 1 ) ) $.

ntp4vcss-in63-definition $a |- (
  NTP4VCIn63 A
) <-> (
  ( -u ( 2 ^ ; 6 2 ) ) <_ A
  /\
  A < ( 2 ^ ; 6 2 )
) $.

${
  $d x A $.

  ntp4vcss-bv63-definition $a |- NTP4VCBV63 = {
    x e. ZZ | ( NTP4VCIn63 x )
  } $.
$}

${
  ntp4vcss-fmap-definition $a |- NTP4VCFMap = {
    f e. _V |
      (
        Fun f
        /\
        (
          dom f C_ NTP4VCByte
          /\
          ran f C_ NTP4VCBV63
        )
      )
  } $.
$}

ntp4vcss-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vcss-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vcss-substring-definition $a |- (
  NTP4VCSubstring A B C
) = (
  A substr
    <.
      ( NTP4VCToNat B ) ,
      ( ( NTP4VCToNat B ) + ( NTP4VCToNat C ) )
    >.
) $.

${
  $d j A B C $.

  ntp4vcss-prefix-present-definition $a |- (
    NTP4VCPrefixPresent A B C
  ) <-> (
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < C
        )
        ->
        ( NTP4VCAt A j ) e. dom B
      )
  ) $.
$}

${
  $d c A B $.

  ntp4vcss-shift-bounds-definition $a |- (
    NTP4VCShiftBounds A B
  ) <-> (
    A. c e. NTP4VCByte
      (
        c e. dom A
        ->
        (
          1 <_ ( A ` c )
          /\
          ( A ` c ) <_ B
        )
      )
  ) $.
$}

${
  $d c j A B $.

  ntp4vcss-final-no-occurrence-definition $a |- (
    NTP4VCFinalNoOccurrence A B
  ) <-> (
    A. c e. NTP4VCByte
      (
        c e. dom B
        ->
        A. j e. ZZ
          (
            (
              1 <_ j
              /\
              j < ( B ` c )
            )
            ->
            (
              NTP4VCAt A ( ( # ` A ) - j )
            ) =/= c
          )
      )
  ) $.
$}

ntp4vcss-bad-shift-invariant-definition $a |- (
  NTP4VCBadShiftInvariant A B
) <-> (
  ( NTP4VCPrefixPresent A B ( # ` A ) )
  /\
  (
    ( NTP4VCShiftBounds B ( ( # ` A ) + 1 ) )
    /\
    ( NTP4VCFinalNoOccurrence A B )
  )
) $.

ntp4vcss-matches-definition $a |- (
  NTP4VCMatches A B C
) <-> (
  (
    0 <_ C
    /\
    C <_ ( ( # ` B ) - ( # ` A ) )
  )
  /\
  (
    NTP4VCSubstring B C ( # ` A )
  ) = A
) $.

${
  $d j A B C D E $.

  $(
    A=pattern, B=text, C=pattern length, D=text length, E=upper index.
  $)
  ntp4vcss-no-match-before-definition $a |- (
    NTP4VCNoMatchBefore A B C D E
  ) <-> (
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < E
        )
        ->
        (
          j <_ ( D - C )
          ->
          (
            NTP4VCSubstring B j C
          ) =/= A
        )
      )
  ) $.
$}

ntp4vcss-search-invariant-definition $a |- (
  NTP4VCSearchInvariant A B C D E
) <-> (
  (
    0 <_ E
    /\
    E <_ D
  )
  /\
  (
    NTP4VCNoMatchBefore A B C D E
  )
) $.

${
  $d j A B C $.

  ntp4vcss-search-post-definition $a |- (
    NTP4VCSearchPost A B C
  ) <-> (
    (
      ( -u 1 ) <_ C
      /\
      C <_ ( ( # ` B ) - ( # ` A ) )
    )
    /\
    (
      (
        C = ( -u 1 )
        /\
        A. j e. ZZ
          -.
          ( NTP4VCMatches A B j )
      )
      \/
      (
        C =/= ( -u 1 )
        /\
        ( NTP4VCMatches A B C )
      )
    )
  ) $.
$}

ntp4vcss-shift-availability-definition $a |- (
  NTP4VCShiftAvailability A B C
) <-> (
  (
    B e. dom A
    /\
    B e. dom A
  )
  \/
  (
    -. B e. dom A
    /\
    ( NTP4VCIn63 ( C + 1 ) )
  )
) $.

ntp4vcss-shift-value-definition $a |- (
  NTP4VCShiftValue A B C D
) <-> (
  (
    B e. dom A
    /\
    (
      D = ( A ` B )
      /\
      D = ( A ` B )
    )
  )
  \/
  (
    -. B e. dom A
    /\
    D = ( C + 1 )
  )
) $.

${
  $d o A B C D E F $.

  $(
    A=pattern, B=text, C=pattern length, D=text length, E=index, F=shift.
  $)
  ntp4vcss-after-shift-definition $a |- (
    NTP4VCAfterShift A B C D E F
  ) <-> (
    ( NTP4VCIn63 ( E + F ) )
    /\
    A. o e. NTP4VCBV63
      (
        o = ( E + F )
        ->
        (
          (
            0 <_ ( ( D - C ) - E )
            /\
            ( ( D - C ) - o ) < ( ( D - C ) - E )
          )
          /\
          (
            (
              0 <_ o
              /\
              o <_ D
            )
            /\
            ( NTP4VCNoMatchBefore A B C D o )
          )
        )
      )
  ) $.
$}

${
  $d o A B C D E F G $.

  $(
    A=pattern, B=text, C=map, D=pattern length, E=text length,
    F=index, G=offset.
  $)
  ntp4vcss-read-character-definition $a |- (
    NTP4VCReadCharacter A B C D E F G
  ) <-> (
    (
      NTP4VCShiftAvailability
        C ( NTP4VCAt B G ) D
    )
    /\
    A. o e. NTP4VCBV63
      (
        (
          NTP4VCShiftValue
            C ( NTP4VCAt B G ) D o
        )
        ->
        (
          NTP4VCAfterShift
            A B D E F o
        )
      )
  ) $.
$}

${
  $d o A B C D E F $.

  $(
    A=pattern, B=text, C=map, D=pattern length, E=text length, F=index.
  $)
  ntp4vcss-advance-definition $a |- (
    NTP4VCAdvance A B C D E F
  ) <-> (
    ( NTP4VCIn63 ( F + D ) )
    /\
    A. o e. NTP4VCBV63
      (
        o = ( F + D )
        ->
        (
          (
            0 <_ o
            /\
            o < ( # ` B )
          )
          /\
          (
            NTP4VCReadCharacter
              A B C D E F o
          )
        )
      )
  ) $.
$}

${
  $d o A B C D E F $.

  $(
    A=pattern, B=text, C=map, D=pattern length, E=text length, F=index.
  $)
  ntp4vcss-after-failed-definition $a |- (
    NTP4VCAfterFailed A B C D E F
  ) <-> (
    ( NTP4VCIn63 ( E - D ) )
    /\
    A. o e. NTP4VCBV63
      (
        o = ( E - D )
        ->
        (
          ( F = o -> F = o )
          ->
          (
            (
              F = o
              /\
              ( NTP4VCSearchPost A B ( -u 1 ) )
            )
            \/
            (
              F =/= o
              /\
              ( NTP4VCAdvance A B C D E F )
            )
          )
        )
      )
  ) $.
$}

ntp4vcss-guard-true-definition $a |- (
  NTP4VCGuardTrue A B C D E F
) <-> (
  (
    0 <_ F
    /\
    F <_ ( ( # ` B ) - ( # ` A ) )
  )
  /\
  (
    (
      ( NTP4VCMatches A B F )
      /\
      ( NTP4VCSearchPost A B F )
    )
    \/
    (
      -.
      ( NTP4VCMatches A B F )
      /\
      ( NTP4VCAfterFailed A B C D E F )
    )
  )
) $.

${
  $d o A B C D E F $.

  $(
    A=pattern, B=text, C=map, D=pattern length, E=text length, F=index.
  $)
  ntp4vcss-iteration-definition $a |- (
    NTP4VCIteration A B C D E F
  ) <-> (
    ( NTP4VCIn63 ( E - D ) )
    /\
    A. o e. NTP4VCBV63
      (
        o = ( E - D )
        ->
        (
          (
            F <_ o
            /\
            ( NTP4VCGuardTrue A B C D E F )
          )
          \/
          (
            -. F <_ o
            /\
            ( NTP4VCSearchPost A B ( -u 1 ) )
          )
        )
      )
  ) $.
$}

${
  $d i A B C D E $.

  $(
    A=pattern, B=text, C=map, D=pattern-length word, E=text-length word.
  $)
  ntp4vcss-search-body-definition $a |- (
    NTP4VCSearchBody A B C D E
  ) <-> (
    (
      (
        0 <_ 0
        /\
        0 <_ E
      )
      /\
      ( NTP4VCNoMatchBefore A B D E 0 )
    )
    /\
    A. i e. NTP4VCBV63
      (
        ( NTP4VCSearchInvariant A B D E i )
        ->
        ( NTP4VCIteration A B C D E i )
      )
  ) $.
$}

${
  $d m n A B C $.

  ntp4vcss-search-vc-definition $a |- (
    NTP4VCSearchVC A B C
  ) <-> (
    A. m e. NTP4VCBV63
      (
        (
          m = ( # ` A )
          /\
          0 <_ ( # ` A )
        )
        ->
        A. n e. NTP4VCBV63
          (
            (
              n = ( # ` B )
              /\
              0 <_ ( # ` B )
            )
            ->
            ( NTP4VCSearchBody A B C m n )
          )
      )
  ) $.
$}

${
  $d a b A B C D E F G $.

  $( Source bad-shift-table carrier and abstract map implementation carrier. $)
  ntp4vcss-bst-carrier-set $e |- A e. _V $.
  ntp4vcss-bst-carrier-nonempty $e |- A =/= (/) $.
  ntp4vcss-table-carrier-set $e |- B e. _V $.
  ntp4vcss-table-carrier-nonempty $e |- B =/= (/) $.

  $( Source record projections pat and sht, and the to_fmap projection. $)
  ntp4vcss-pattern-function
    $e |- C e. ( ( Word NTP4VCByte ) ^m A ) $.
  ntp4vcss-table-function
    $e |- D e. ( B ^m A ) $.
  ntp4vcss-to-fmap-function
    $e |- E e. ( NTP4VCFMap ^m B ) $.

  $( Source bad_shift_table record extensionality. $)
  ntp4vcss-record-extensionality $e |- A. a e. A
    A. b e. A
      (
        (
          ( C ` a ) = ( C ` b )
          /\
          ( D ` a ) = ( D ` b )
        )
        ->
        a = b
      ) $.

  $( Complete source bad_shift_table record invariant. $)
  ntp4vcss-record-invariant $e |- A. b e. A
    (
      NTP4VCBadShiftInvariant
        ( C ` b )
        ( E ` ( D ` b ) )
    ) $.

  $( Source theorem parameters bst and text, followed by fact0. $)
  ntp4vcss-bst $e |- F e. A $.
  ntp4vcss-text $e |- G e. Word NTP4VCByte $.
  ntp4vcss-fact0 $e |- ( # ` ( C ` F ) ) <_ ( # ` G ) $.

  ntp4vcss-pearl-string-search-bad-shift-table-search-vc
    $a |- (
      NTP4VCSearchVC
        ( C ` F )
        G
        ( E ` ( D ` F ) )
    ) $.
$}
