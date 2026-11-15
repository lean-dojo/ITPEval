$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_Simple_queryqtvc: the simple linear range-query verification
  condition initializes and preserves an integer half-open range sum and
  returns the sum over the requested array interval. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat and
  NTP4VCAt reproduce Int.toNat and totalized list lookup with default zero.

  NTP4VCSum is the finite integer sum over the indicated half-open interval.
  Under the VC's bounds it is definitionally equivalent to the source
  ArraySum.sum. The source let-bound value o1 is inlined as C - 1, preserving
  both guarded loop-range branches. The scoped essential hypotheses are
  precisely the array and integer parameter types and the three source
  preconditions. The nested quantifiers over the accumulator s and loop index
  k retain their full integer domains.

  The final declaration is Metamath's native unproved $a statement encoding;
  every preceding $a is syntax or a faithful definition required to state it,
  and this artifact contains no $p proof declaration.
$)

$c NTP4VCToNat NTP4VCAt NTP4VCSum $.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-sum-syntax
  $a class ( NTP4VCSum A B C ) $.

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
  $d s A B C $.
  $d k A B C s $.

  $( Source parameters: A=a, B=i, and C=j; s and k are internal states. $)

  ntp4vc-a-list $e |- A e. Word ZZ $.
  ntp4vc-i-integer $e |- B e. ZZ $.
  ntp4vc-j-integer $e |- C e. ZZ $.

  ntp4vc-i-nonnegative $e |- 0 <_ B $.
  ntp4vc-i-le-j $e |- B <_ C $.
  ntp4vc-j-at-most-length $e |- C <_ ( # ` A ) $.

  ntp4vc-pearl-sumrange-simple-query-vc $a |- (
    (
      B <_ ( ( C - 1 ) + 1 )
      ->
      (
        0 = ( NTP4VCSum A B B )
        /\
        A. s e. ZZ
          (
            A. k e. ZZ
              (
                (
                  (
                    B <_ k
                    /\
                    k <_ ( C - 1 )
                  )
                  /\
                  s = ( NTP4VCSum A B k )
                )
                ->
                (
                  (
                    0 <_ k
                    /\
                    k < ( # ` A )
                  )
                  /\
                  (
                    s + ( NTP4VCAt A k )
                  )
                  =
                  ( NTP4VCSum A B ( k + 1 ) )
                )
              )
            /\
            (
              s = ( NTP4VCSum A B ( ( C - 1 ) + 1 ) )
              ->
              s = ( NTP4VCSum A B C )
            )
          )
      )
    )
    /\
    (
      ( ( C - 1 ) + 1 ) < B
      ->
      0 = ( NTP4VCSum A B C )
    )
  ) $.
$}
