$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_ghc_sortqtvc
  (ntp4vc__metamath__pearl/verifythis_2019_ghc_sort_Top_ghc_sortqtvc):
  the top-level GHC-sort verification condition states that the empty input
  is already a sorted permutation and that copying any sorted list with the
  same integer multiplicities into a nonempty input yields a sorted
  permutation of the original list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer lists. NTP4VCToNat reproduces
  the exported integer-to-natural conversion, and NTP4VCAt is integer-indexed
  lookup with default zero outside [0, length).

  NTP4VCOcc is the cardinality of all integer positions in the half-open
  interval [0, length) at which the list has the requested value. It is
  therefore both the source map occurrence count over that interval and the
  source finite-list count. NTP4VCPerm compares these multiplicities for
  every integer and includes equal length, which is equivalent in both
  directions to List.Perm on finite integer lists.

  NTP4VCSorted is the source IntArraySorted.sorted predicate. The source
  inductive sorted1 predicate has exactly the same extension on finite
  integer lists: its constructors characterize nondecreasing adjacent
  entries, equivalently every pair of indices i <= j is nondecreasing.

  NTP4VCCopyPremise retains the copied-list equation, the unchanged empty
  prefix equation, and the occurrence equation. NTP4VCLObligation retains
  the sortedness, occurrence, and length premise for the internally
  quantified list, the zero-offset arithmetic obligations, and the
  internally quantified post-copy list. NTP4VCGhcSortVC represents the
  proposition-valued source conditional by its equivalent exhaustive
  equality and disequality branches. Every source integer and list
  quantifier remains at its original scope. The final declaration is
  Metamath's native unproved $a statement encoding; every preceding $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCOcc
  NTP4VCSorted NTP4VCPerm
  NTP4VCCopyPremise NTP4VCLObligation NTP4VCGhcSortVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-occ-syntax
  $a class ( NTP4VCOcc A B ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A ) $.
ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-copy-premise-syntax
  $a wff ( NTP4VCCopyPremise A B C ) $.
ntp4vc-l-obligation-syntax
  $a wff ( NTP4VCLObligation A B ) $.
ntp4vc-ghc-sort-vc-syntax
  $a wff ( NTP4VCGhcSortVC A ) $.

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
  $d k A B $.

  ntp4vc-occ-definition $a |- (
    NTP4VCOcc A B
  ) = (
    # `
    { k e. ZZ |
      (
        (
          0 <_ k
          /\
          k < ( # ` A )
        )
        /\
        ( NTP4VCAt A k ) = B
      )
    }
  ) $.
$}

${
  $d i j A $.

  ntp4vc-sorted-definition $a |- (
    NTP4VCSorted A
  ) <->
  (
    A e. Word ZZ
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            0 <_ i
            /\
            (
              i <_ j
              /\
              j < ( # ` A )
            )
          )
          ->
          ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
        )
  ) $.
$}

${
  $d v A B $.

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
          ( NTP4VCOcc A v )
          =
          ( NTP4VCOcc B v )
        )
    )
  ) $.
$}

${
  $d x y A B $.

  ntp4vc-copy-premise-definition $a |- (
    NTP4VCCopyPremise A B C
  ) <->
  (
    (
      A. x e. ZZ
        (
          (
            0 <_ x
            /\
            x < ( # ` A )
          )
          ->
          (
            NTP4VCAt A x
          )
          =
          (
            NTP4VCAt B ( x - 0 )
          )
        )
      /\
      A. x e. ZZ
        (
          (
            0 <_ x
            /\
            x < 0
          )
          ->
          (
            NTP4VCAt A x
          )
          =
          (
            NTP4VCAt C x
          )
        )
    )
    /\
    A. x e. ZZ
      (
        ( NTP4VCOcc A x )
        =
        ( NTP4VCOcc B x )
      )
  ) $.
$}

${
  $d x A B C $.

  ntp4vc-l-obligation-definition $a |- (
    NTP4VCLObligation A B
  ) <->
  (
    (
      (
        NTP4VCSorted B
        /\
        A. x e. ZZ
          (
            ( NTP4VCOcc A x )
            =
            ( NTP4VCOcc B x )
          )
      )
      /\
      ( # ` B ) = ( # ` A )
    )
    ->
    (
      (
        0 <_ 0
        /\
        ( # ` B ) = ( ( # ` A ) - 0 )
      )
      /\
      A. y e. Word ZZ
        (
          ( # ` y ) = ( # ` A )
          ->
          (
            ( NTP4VCCopyPremise y B A )
            ->
            (
              ( NTP4VCSorted y )
              /\
              ( NTP4VCPerm y A )
            )
          )
        )
    )
  ) $.
$}

ntp4vc-ghc-sort-vc-definition $a |- (
  NTP4VCGhcSortVC A
) <->
(
  (
    ( # ` A ) = 0
    /\
    (
      ( NTP4VCSorted A )
      /\
      ( NTP4VCPerm A A )
    )
  )
  \/
  (
    -. ( # ` A ) = 0
    /\
    (
      0 < ( # ` A )
      /\
      A. l e. Word ZZ
        ( NTP4VCLObligation A l )
    )
  )
) $.

${
  ntp4vc-input-list $e |- A e. Word ZZ $.

  ntp4vc-pearl-verifythis-2019-ghc-sort-top-ghc-sort-vc
    $a |- ( NTP4VCGhcSortVC A ) $.
$}
