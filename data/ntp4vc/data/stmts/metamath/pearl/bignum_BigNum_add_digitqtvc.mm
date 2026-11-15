$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bignum_BigNum_add_digitqtvc: the big-number add-digit verification
  condition states the validity and numerical-value obligations for adding
  one base-b digit to a little-endian integer list. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCTail is the source
  list tail on every nonempty word. NTP4VCValue is the finite positional sum
  sum_k digit[k] * base^k, which is bidirectionally equivalent to the source
  recursion value [] = 0 and value (d :: r) = d + base * value r.

  NTP4VCValid requires every digit to be below the base, every non-leading
  digit to be nonnegative, and the final digit of a nonempty word to be
  positive. This is exactly the source recursion distinguishing the empty,
  singleton, and longer-list cases.

  NTP4VCFirst and NTP4VCPremise expand the source list matches and
  proposition-valued conditionals into exhaustive guarded disjunctions.
  Source constructor results are singleton-word concatenations, and the
  recursive carry result remains internally existentially quantified over
  every integer word. Splitting the theorem parameters and assumptions into
  scoped essential hypotheses is bidirectionally equivalent to the source
  theorem context. The unused digit and num carriers do not occur in the
  verification condition and are conservatively omitted. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCTail NTP4VCValue NTP4VCValid
  NTP4VCFirst NTP4VCPremise
$.

ntp4vc-tail-syntax $a class ( NTP4VCTail A ) $.
ntp4vc-value-syntax $a class ( NTP4VCValue A B ) $.
ntp4vc-valid-syntax $a wff ( NTP4VCValid A B ) $.
ntp4vc-first-syntax $a wff ( NTP4VCFirst A B C ) $.
ntp4vc-premise-syntax $a wff ( NTP4VCPremise A B C D ) $.

${
  $d k A $.

  ntp4vc-tail-definition $a |- (
    NTP4VCTail A
  ) = (
    k e. ( 0 ..^ ( ( # ` A ) - 1 ) ) |->
      ( A ` ( k + 1 ) )
  ) $.
$}

${
  $d k A B $.

  ntp4vc-value-definition $a |- (
    NTP4VCValue A B
  ) = (
    sum_ k e. ( 0 ..^ ( # ` B ) )
      ( ( B ` k ) x. ( A ^ k ) )
  ) $.
$}

${
  $d k A B $.

  ntp4vc-valid-definition $a |- (
    NTP4VCValid A B
  ) <-> (
    B e. Word ZZ
    /\
    (
      ( # ` B ) = 0
      \/
      (
        0 < ( # ` B )
        /\
        A. k e. ( 0 ..^ ( # ` B ) )
          (
            ( B ` k ) < A
            /\
            (
              (
                k = ( ( # ` B ) - 1 )
                ->
                0 < ( B ` k )
              )
              /\
              (
                k < ( ( # ` B ) - 1 )
                ->
                0 <_ ( B ` k )
              )
            )
          )
      )
    )
  ) $.
$}

ntp4vc-first-definition $a |- (
  NTP4VCFirst A B C
) <-> (
  ( # ` B ) = 0
  \/
  (
    0 < ( # ` B )
    /\
    (
      -. ( ( C + ( B ` 0 ) ) < A )
      ->
      (
        ( NTP4VCTail B ) = ( NTP4VCTail B )
        /\
        (
          ( NTP4VCValid A ( NTP4VCTail B ) )
          /\
          (
            0 <_ 1
            /\
            1 < A
          )
        )
      )
    )
  )
) $.

${
  $d o A B C D $.

  ntp4vc-premise-definition $a |- (
    NTP4VCPremise A B C D
  ) <-> (
    (
      ( # ` B ) = 0
      /\
      (
        (
          C = 0
          /\
          D = (/)
        )
        \/
        (
          -. ( C = 0 )
          /\
          D = <" C ">
        )
      )
    )
    \/
    (
      0 < ( # ` B )
      /\
      (
        (
          ( C + ( B ` 0 ) ) < A
          /\
          D = (
            <" ( C + ( B ` 0 ) ) ">
            ++
            ( NTP4VCTail B )
          )
        )
        \/
        (
          -. ( ( C + ( B ` 0 ) ) < A )
          /\
          E. o e. Word ZZ
            (
              (
                ( NTP4VCValid A o )
                /\
                (
                  ( NTP4VCValue A o )
                  =
                  ( ( NTP4VCValue A ( NTP4VCTail B ) ) + 1 )
                )
              )
              /\
              D = (
                <" ( ( C + ( B ` 0 ) ) - A ) ">
                ++
                o
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d r A B C $.

  $( Source parameters: A=base, B=n, and C=d. $)

  ntp4vc-base-integer $e |- A e. ZZ $.
  ntp4vc-base-lower-bound $e |- 1 < A $.
  ntp4vc-n-list $e |- B e. Word ZZ $.
  ntp4vc-d-integer $e |- C e. ZZ $.

  ntp4vc-n-valid $e |- ( NTP4VCValid A B ) $.
  ntp4vc-d-nonnegative $e |- 0 <_ C $.
  ntp4vc-d-below-base $e |- C < A $.

  ntp4vc-pearl-bignum-add-digit-vc $a |- (
    ( NTP4VCFirst A B C )
    /\
    A. r e. Word ZZ
      (
        ( NTP4VCPremise A B C r )
        ->
        (
          ( NTP4VCValid A r )
          /\
          (
            ( NTP4VCValue A r )
            =
            ( ( NTP4VCValue A B ) + C )
          )
        )
      )
  ) $.
$}
