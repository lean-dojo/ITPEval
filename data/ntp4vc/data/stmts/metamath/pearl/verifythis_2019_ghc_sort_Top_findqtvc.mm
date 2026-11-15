$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_findqtvc
  (ntp4vc__metamath__pearl/verifythis_2019_ghc_sort_Top_findqtvc):
  the recursive verification condition for finding an integer value in a
  nonempty half-open sequence interval with a positive occurrence count.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat and
  NTP4VCAt reproduce the exported integer-to-natural conversion and totalized
  sequence lookup; the default zero is immaterial wherever the source lookup
  is active because the verification condition supplies its index bounds.

  NTP4VCOcc is the cardinality of positions in the Why3 half-open interval
  [lower, upper) whose sequence value equals the requested integer. This
  follows the primary Why3 SO.occ specification directly, rather than the
  secondary exports' proposition-changing drop-after-take rendering.

  NTP4VCRecursiveCall is the complete variant, recursive precondition, and
  positive-occurrence obligation at start + 1. NTP4VCResultPremise replaces
  the proposition-valued source conditional by its equivalent exhaustive
  guarded disjunction. NTP4VCFindVC retains the source conjunction and keeps
  the result integer universally quantified at its internal scope.

  Splitting the four typed parameters and four assumptions into scoped
  essential hypotheses is bidirectionally equivalent to the source curried
  theorem. Every auxiliary $a declaration is syntax or an explicit faithful
  definition. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCOcc
  NTP4VCRecursiveCall NTP4VCResultPremise
  NTP4VCResultPostcondition NTP4VCFindVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-occ-syntax
  $a class ( NTP4VCOcc A B C D ) $.

ntp4vc-recursive-call-syntax
  $a wff ( NTP4VCRecursiveCall A B C D ) $.
ntp4vc-result-premise-syntax
  $a wff ( NTP4VCResultPremise A B C D E ) $.
ntp4vc-result-postcondition-syntax
  $a wff ( NTP4VCResultPostcondition A B C D E ) $.
ntp4vc-find-vc-syntax
  $a wff ( NTP4VCFindVC A B C D ) $.

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
  $d k A B C D $.

  ntp4vc-occ-definition $a |- (
    NTP4VCOcc A B C D
  ) = (
    # `
    { k e. ZZ |
      (
        (
          C <_ k
          /\
          k < D
        )
        /\
        ( NTP4VCAt A k ) = B
      )
    }
  ) $.
$}

ntp4vc-recursive-call-definition $a |- (
  NTP4VCRecursiveCall A B C D
) <->
(
  (
    0 <_ ( D - C )
    /\
    ( D - ( C + 1 ) ) < ( D - C )
  )
  /\
  (
    (
      0 <_ ( C + 1 )
      /\
      (
        ( C + 1 ) < D
        /\
        D <_ ( # ` A )
      )
    )
    /\
    1 <_ ( NTP4VCOcc A B ( C + 1 ) D )
  )
) $.

ntp4vc-result-premise-definition $a |- (
  NTP4VCResultPremise A B C D E
) <->
(
  (
    ( NTP4VCAt A C ) = B
    /\
    E = C
  )
  \/
  (
    -. ( NTP4VCAt A C ) = B
    /\
    (
      (
        ( C + 1 ) <_ E
        /\
        E < D
      )
      /\
      ( NTP4VCAt A E ) = B
    )
  )
) $.

ntp4vc-result-postcondition-definition $a |- (
  NTP4VCResultPostcondition A B C D E
) <->
(
  (
    C <_ E
    /\
    E < D
  )
  /\
  ( NTP4VCAt A E ) = B
) $.

${
  $d r A B C D $.

  ntp4vc-find-vc-definition $a |- (
    NTP4VCFindVC A B C D
  ) <->
  (
    (
      -. ( NTP4VCAt A C ) = B
      ->
      ( NTP4VCRecursiveCall A B C D )
    )
    /\
    A. r e. ZZ
      (
        ( NTP4VCResultPremise A B C D r )
        ->
        ( NTP4VCResultPostcondition A B C D r )
      )
  ) $.
$}

${
  $d r A B C D $.

  $( Source theorem parameters: A=s, B=e, C=seq1, and D=v. $)

  ntp4vc-s-integer $e |- A e. ZZ $.
  ntp4vc-e-integer $e |- B e. ZZ $.
  ntp4vc-seq1-list $e |- C e. Word ZZ $.
  ntp4vc-v-integer $e |- D e. ZZ $.

  ntp4vc-s-nonnegative $e |- 0 <_ A $.
  ntp4vc-s-less-than-e $e |- A < B $.
  ntp4vc-e-in-bounds $e |- B <_ ( # ` C ) $.
  ntp4vc-positive-occurrence $e |- 1 <_ (
    NTP4VCOcc C D A B
  ) $.

  ntp4vc-pearl-verifythis-2019-ghc-sort-find-vc
    $a |- ( NTP4VCFindVC C D A B ) $.
$}
