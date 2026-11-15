$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_orderqtvc
  (ntp4vc__metamath__pearl/verifythis_2019_ghc_sort_Top_orderqtvc):
  the GHC-sort order verification condition states that an integer list
  known to be strictly increasing or nonincreasing is returned unchanged or
  reversed according to its first two elements, producing a nondecreasing
  permutation of the input. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer lists. NTP4VCReverse is exact
  finite-word reversal.

  NTP4VCStrictIncreasing, NTP4VCNondecreasing, and
  NTP4VCNonincreasing characterize every ordered pair of positions. Over the
  transitive integer orders these are bidirectionally equivalent to the
  source inductive StrictIncr.sorted, Incr.sorted, and Decr.sorted predicates,
  including their empty and singleton cases.

  NTP4VCPerm compares the multiplicity of every integer and retains equal
  length, which is equivalent in both directions to the source finite-list
  permutation relation. NTP4VCOrderResult is the exact graph of the source
  list match: lists of length zero or one are unchanged, while longer lists
  are unchanged when their first element is strictly below their second and
  are otherwise reversed. Thus the result witness remains universally
  quantified at its source-internal scope.

  NTP4VCOrderVC retains the generated match-safety conjunct as T. and the
  complete universally quantified postcondition. Splitting the typed input
  and monotonicity assumption into scoped essential hypotheses is
  bidirectionally equivalent to the source curried theorem. Every auxiliary
  $a declaration is syntax or an explicit faithful definition. The final $a
  declaration is Metamath's native unproved statement encoding, and this
  database contains no $p declaration.
$)

$c
  NTP4VCReverse
  NTP4VCStrictIncreasing NTP4VCNondecreasing NTP4VCNonincreasing
  NTP4VCPerm NTP4VCOrderResult NTP4VCOrderVC
$.

ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-strict-increasing-syntax
  $a wff ( NTP4VCStrictIncreasing A ) $.
ntp4vc-nondecreasing-syntax
  $a wff ( NTP4VCNondecreasing A ) $.
ntp4vc-nonincreasing-syntax
  $a wff ( NTP4VCNonincreasing A ) $.
ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-order-result-syntax
  $a wff ( NTP4VCOrderResult A B ) $.
ntp4vc-order-vc-syntax
  $a wff ( NTP4VCOrderVC A ) $.

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

${
  $d i j A $.

  ntp4vc-strict-increasing-definition $a |- (
    NTP4VCStrictIncreasing A
  ) <->
  (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) < ( A ` j )
        )
  ) $.
$}

${
  $d i j A $.

  ntp4vc-nondecreasing-definition $a |- (
    NTP4VCNondecreasing A
  ) <->
  (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) <_ ( A ` j )
        )
  ) $.
$}

${
  $d i j A $.

  ntp4vc-nonincreasing-definition $a |- (
    NTP4VCNonincreasing A
  ) <->
  (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` j ) <_ ( A ` i )
        )
  ) $.
$}

${
  $d k v A B $.

  ntp4vc-perm-definition $a |- (
    NTP4VCPerm A B
  ) <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. ZZ
        (
          (
            # `
            { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
          )
          =
          (
            # `
            { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
          )
        )
    )
  ) $.
$}

ntp4vc-order-result-definition $a |- (
  NTP4VCOrderResult A B
) <->
(
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    (
      ( # ` A ) < 2
      /\
      B = A
    )
    \/
    (
      2 <_ ( # ` A )
      /\
      (
        (
          ( A ` 0 ) < ( A ` 1 )
          /\
          B = A
        )
        \/
        (
          -. ( A ` 0 ) < ( A ` 1 )
          /\
          B = ( NTP4VCReverse A )
        )
      )
    )
  )
) $.

${
  $d r A $.

  ntp4vc-order-vc-definition $a |- (
    NTP4VCOrderVC A
  ) <->
  (
    T.
    /\
    A. r e. Word ZZ
      (
        ( NTP4VCOrderResult A r )
        ->
        (
          ( NTP4VCNondecreasing r )
          /\
          ( NTP4VCPerm A r )
        )
      )
  ) $.
$}

${
  ntp4vc-l-list $e |- A e. Word ZZ $.
  ntp4vc-fact0 $e |- (
    ( NTP4VCStrictIncreasing A )
    \/
    ( NTP4VCNonincreasing A )
  ) $.

  ntp4vc-pearl-verifythis-2019-ghc-sort-top-order-vc
    $a |- ( NTP4VCOrderVC A ) $.
$}
