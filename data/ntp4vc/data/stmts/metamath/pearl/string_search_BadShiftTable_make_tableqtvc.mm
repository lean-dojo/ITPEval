$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/string_search_BadShiftTable_make_tableqtvc: the verification
  condition for constructing a bad-character shift table over a byte string,
  including signed 63-bit bounds, finite-map updates, loop invariants, and the
  final shift-table invariant. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCByte is the complete 8-bit character carrier. NTP4VCBV63 is the
  complete signed-value image of 63-bit words; signed value is a bijection
  from source words to this integer interval. SetMM words over NTP4VCByte are
  exactly arbitrary finite source strings.

  NTP4VCFMap is the full carrier of finite partial functions from bytes to
  signed 63-bit values. Since the byte domain is finite, every such partial
  function is finite. Domain membership, function application on a present
  key, the empty function, and NTP4VCMapUpdate are exactly finite-map
  membership, lookup, empty, and insertion.

  T remains the arbitrary inhabited source implementation carrier t int63,
  and F remains its arbitrary total to_fmap projection. Thus quantification
  over implementation values is not replaced by quantification over maps.
  NTP4VCToNat and NTP4VCAt reproduce source integer-to-natural conversion and
  totalized string lookup. The invariant predicates and continuation
  predicates are biconditional factorizations of the original verification
  condition. Eliminating the source's universally quantified character
  immediately constrained to equal pat[j] is bidirectionally equivalent to
  direct membership of pat[j].

  Expanding the definitions recovers every source domain, assumption,
  quantifier, bound, implication, conjunction, map-update premise, loop
  initialization and preservation obligation, and final invariant. The last
  $a declaration is Metamath's native unproved statement encoding; every
  preceding $a is syntax or a faithful definition required to state it, and
  this database contains no $p proof declaration.
$)

$c
  NTP4VCByte NTP4VCIn63 NTP4VCBV63 NTP4VCFMap
  NTP4VCToNat NTP4VCAt NTP4VCMapUpdate
  NTP4VCPrefixPresent NTP4VCShiftBounds NTP4VCNoRecent
  NTP4VCLoopInvariant NTP4VCFinalNoOccurrence NTP4VCFinalInvariant
  NTP4VCUpdateObligation NTP4VCIterationResult
  NTP4VCIterationObligation NTP4VCTablePackage
  NTP4VCPositiveCase NTP4VCNegativeCase NTP4VCMakeTableConclusion
$.

ntp4vc-byte-syntax $a class NTP4VCByte $.
ntp4vc-in63-syntax $a wff ( NTP4VCIn63 A ) $.
ntp4vc-bv63-syntax $a class NTP4VCBV63 $.
ntp4vc-fmap-syntax $a class NTP4VCFMap $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-map-update-syntax
  $a class ( NTP4VCMapUpdate A B C ) $.

ntp4vc-prefix-present-syntax
  $a wff ( NTP4VCPrefixPresent A B C ) $.
ntp4vc-shift-bounds-syntax
  $a wff ( NTP4VCShiftBounds A B ) $.
ntp4vc-no-recent-syntax
  $a wff ( NTP4VCNoRecent A B C D ) $.
ntp4vc-loop-invariant-syntax
  $a wff ( NTP4VCLoopInvariant A B C D ) $.
ntp4vc-final-no-occurrence-syntax
  $a wff ( NTP4VCFinalNoOccurrence A B ) $.
ntp4vc-final-invariant-syntax
  $a wff ( NTP4VCFinalInvariant A B ) $.
ntp4vc-update-obligation-syntax
  $a wff ( NTP4VCUpdateObligation A B C D E F ) $.
ntp4vc-iteration-result-syntax
  $a wff ( NTP4VCIterationResult A B C D E F ) $.
ntp4vc-iteration-obligation-syntax
  $a wff ( NTP4VCIterationObligation A B C D E F ) $.
ntp4vc-table-package-syntax
  $a wff ( NTP4VCTablePackage A B C D E F ) $.
ntp4vc-positive-case-syntax
  $a wff ( NTP4VCPositiveCase A B C D E F ) $.
ntp4vc-negative-case-syntax
  $a wff ( NTP4VCNegativeCase A B C D ) $.
ntp4vc-make-table-conclusion-syntax
  $a wff ( NTP4VCMakeTableConclusion A B C D E ) $.

ntp4vc-byte-definition $a |- NTP4VCByte =
  ( 0 ... ( ( 2 ^ 8 ) - 1 ) ) $.

ntp4vc-in63-definition $a |- (
  NTP4VCIn63 A
) <-> (
  ( -u ( 2 ^ ; 6 2 ) ) <_ A
  /\
  A < ( 2 ^ ; 6 2 )
) $.

${
  $d x A $.

  ntp4vc-bv63-definition $a |- NTP4VCBV63 = {
    x e. ZZ | ( NTP4VCIn63 x )
  } $.
$}

${
  ntp4vc-fmap-definition $a |- NTP4VCFMap = {
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
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d k A B C $.

  ntp4vc-map-update-definition $a |- (
    NTP4VCMapUpdate A B C
  ) = (
    k e. ( dom A u. { B } ) |->
      if (
        k = B ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d j A B C $.

  ntp4vc-prefix-present-definition $a |- (
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

  ntp4vc-shift-bounds-definition $a |- (
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
  $d c j A B C D $.

  ntp4vc-no-recent-definition $a |- (
    NTP4VCNoRecent A B C D
  ) <-> (
    A. c e. NTP4VCByte
      (
        c e. dom C
        ->
        A. j e. ZZ
          (
            (
              ( B - ( C ` c ) ) < j
              /\
              j < D
            )
            ->
            ( NTP4VCAt A j ) =/= c
          )
      )
  ) $.
$}

ntp4vc-loop-invariant-definition $a |- (
  NTP4VCLoopInvariant A B C D
) <-> (
  ( NTP4VCPrefixPresent A C D )
  /\
  (
    ( NTP4VCShiftBounds C ( B + 1 ) )
    /\
    ( NTP4VCNoRecent A B C D )
  )
) $.

${
  $d c j A B $.

  ntp4vc-final-no-occurrence-definition $a |- (
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

ntp4vc-final-invariant-definition $a |- (
  NTP4VCFinalInvariant A B
) <-> (
  ( NTP4VCPrefixPresent A B ( # ` A ) )
  /\
  (
    ( NTP4VCShiftBounds B ( ( # ` A ) + 1 ) )
    /\
    ( NTP4VCFinalNoOccurrence A B )
  )
) $.

${
  $d q A B C D E F $.

  $(
    A=pattern, B=pattern length, C=to_fmap, D=table before update,
    E=signed loop index, F=new signed-63 value.
  $)
  ntp4vc-update-obligation-definition $a |- (
    NTP4VCUpdateObligation A B C D E F
  ) <-> (
    (
      0 <_ E
      /\
      E < ( # ` A )
    )
    /\
    A. q e. dom C
      (
        ( C ` q )
        =
        (
          NTP4VCMapUpdate
            ( C ` D )
            ( NTP4VCAt A E )
            F
        )
        ->
        (
          NTP4VCLoopInvariant
            A B ( C ` q ) ( E + 1 )
        )
      )
  ) $.
$}

${
  $d o A B C D E F $.

  $(
    A=pattern, B=pattern length, C=implementation carrier,
    D=to_fmap, E=table, F=signed loop index.
  $)
  ntp4vc-iteration-result-definition $a |- (
    NTP4VCIterationResult A B C D E F
  ) <-> (
    ( NTP4VCIn63 ( B - F ) )
    /\
    A. o e. NTP4VCBV63
      (
        o = ( B - F )
        ->
        (
          NTP4VCUpdateObligation
            A B D E F o
        )
      )
  ) $.
$}

${
  $d i A B C D E F $.

  $(
    A=pattern, B=pattern length, C=upper loop word,
    D=implementation carrier, E=to_fmap, F=current table.
  $)
  ntp4vc-iteration-obligation-definition $a |- (
    NTP4VCIterationObligation A B C D E F
  ) <-> (
    A. i e. NTP4VCBV63
      (
        (
          (
            0 <_ i
            /\
            i <_ C
          )
          /\
          (
            NTP4VCLoopInvariant
              A B ( E ` F ) i
          )
        )
        ->
        (
          NTP4VCIterationResult
            A B D E F i
        )
      )
  ) $.
$}

ntp4vc-table-package-definition $a |- (
  NTP4VCTablePackage A B C D E F
) <-> (
  (
    NTP4VCIterationObligation
      A B C D E F
  )
  /\
  (
    (
      NTP4VCLoopInvariant
        A B ( E ` F ) ( C + 1 )
    )
    ->
    ( NTP4VCFinalInvariant A ( E ` F ) )
  )
) $.

${
  $d q A B C D E F $.

  $(
    A=pattern, B=pattern length, C=initial table, D=upper loop word,
    E=implementation carrier, F=to_fmap.
  $)
  ntp4vc-positive-case-definition $a |- (
    NTP4VCPositiveCase A B C D E F
  ) <-> (
    0 <_ ( D + 1 )
    ->
    (
      (
        NTP4VCLoopInvariant
          A B ( F ` C ) 0
      )
      /\
      A. q e. E
        (
          NTP4VCTablePackage
            A B D E F q
        )
    )
  ) $.
$}

ntp4vc-negative-case-definition $a |- (
  NTP4VCNegativeCase A B C D
) <-> (
  C + 1 < 0
  ->
  ( NTP4VCFinalInvariant A ( D ` B ) )
) $.

${
  $d o A B C D E $.

  $(
    A=signed pattern length, B=pattern, C=initial table,
    D=implementation carrier, E=to_fmap.
  $)
  ntp4vc-make-table-conclusion-definition $a |- (
    NTP4VCMakeTableConclusion A B C D E
  ) <-> (
    ( NTP4VCIn63 ( A - 1 ) )
    /\
    A. o e. NTP4VCBV63
      (
        o = ( A - 1 )
        ->
        (
          (
            NTP4VCPositiveCase
              B A C o D E
          )
          /\
          (
            NTP4VCNegativeCase
              B C o E
          )
        )
      )
  ) $.
$}

${
  $d A B C D E $.

  $( Source abstract implementation carrier t int63 and to_fmap. $)
  ntp4vc-table-carrier-set $e |- D e. _V $.
  ntp4vc-table-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-to-fmap-function
    $e |- E e. ( NTP4VCFMap ^m D ) $.

  $( Source theorem parameters m, pat1, and sht1. $)
  ntp4vc-m-word $e |- A e. NTP4VCBV63 $.
  ntp4vc-pattern $e |- B e. Word NTP4VCByte $.
  ntp4vc-initial-table $e |- C e. D $.

  $( Source assumptions fact0, fact1, and fact2. $)
  ntp4vc-fact0 $e |- A = ( # ` B ) $.
  ntp4vc-fact1 $e |- 0 <_ ( # ` B ) $.
  ntp4vc-fact2 $e |- ( E ` C ) = (/) $.

  ntp4vc-pearl-string-search-bad-shift-table-make-table-vc
    $a |- (
      NTP4VCMakeTableConclusion A B C D E
    ) $.
$}
