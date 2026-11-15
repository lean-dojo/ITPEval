$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_queryqtvc: the cumulative-array range-query
  verification condition states that subtracting two cumulative entries
  yields the integer sum over the corresponding half-open array range.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat and
  NTP4VCAt reproduce Int.toNat and totalized list lookup with default zero.

  NTP4VCSum is the finite integer sum over the indicated half-open interval.
  Under the VC's bounds it is definitionally equivalent to the recursively
  specified source ArraySum.sum. NTP4VCCumulative directly expands
  is_cumulative_array_for, preserving its length equation and universally
  quantified prefix-sum condition.

  The scoped essential hypotheses are precisely the two integer-list types,
  the integer-index types, and the four source assumptions. The conclusion
  retains every source bound conjunct and the cumulative-entry difference
  equation. The final declaration is Metamath's native unproved $a statement
  encoding; every preceding $a is syntax or a faithful definition required
  to state it, and this artifact file contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSum NTP4VCCumulative
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-sum-syntax
  $a class ( NTP4VCSum A B C ) $.
ntp4vc-cumulative-syntax
  $a wff ( NTP4VCCumulative A B ) $.

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

  ntp4vc-sum-definition $a |- (
    NTP4VCSum A B C
  ) = sum_ k e.
    (
      ( NTP4VCToNat B )
      ..^
      ( NTP4VCToNat C )
    )
    ( NTP4VCAt A k ) $.
$}

${
  $d i A B $.

  ntp4vc-cumulative-definition $a |- (
    NTP4VCCumulative A B
  ) <->
  (
    ( # ` A ) = ( ( # ` B ) + 1 )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` A )
        )
        ->
        ( NTP4VCAt A i ) = ( NTP4VCSum B 0 i )
      )
  ) $.
$}

${
  $( Source parameters: A=c, B=a, C=i, and D=j. $)

  ntp4vc-c-list $e |- A e. Word ZZ $.
  ntp4vc-a-list $e |- B e. Word ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-j-integer $e |- D e. ZZ $.

  ntp4vc-cumulative-array $e |- ( NTP4VCCumulative A B ) $.
  ntp4vc-i-nonnegative $e |- 0 <_ C $.
  ntp4vc-i-le-j $e |- C <_ D $.
  ntp4vc-j-below-c-length $e |- D < ( # ` A ) $.

  ntp4vc-pearl-sumrange-cumulative-array-query-vc $a |- (
    0 <_ C
    /\
    (
      C < ( # ` A )
      /\
      (
        0 <_ D
        /\
        (
          D < ( # ` A )
          /\
          (
            (
              ( NTP4VCAt A D )
              -
              ( NTP4VCAt A C )
            )
            =
            ( NTP4VCSum B C D )
          )
        )
      )
    )
  ) $.
$}
