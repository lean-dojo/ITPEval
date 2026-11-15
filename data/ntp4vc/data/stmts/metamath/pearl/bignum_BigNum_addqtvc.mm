$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bignum_BigNum_addqtvc: the big-number addition verification
  condition states validity and numerical-value preservation for adding two
  little-endian base-b integer lists. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCValue is the
  finite positional sum sum_k digit[k] * base^k, which is bidirectionally
  equivalent to the source recursion value [] = 0 and
  value (d :: r) = d + base * value r.

  NTP4VCValid requires every digit to be below the base, every non-leading
  digit to be nonnegative, and the final digit of a nonempty word to be
  positive. This is exactly the source recursion distinguishing the empty,
  singleton, and longer-list cases.

  Splitting the base declaration, theorem parameters, and assumptions into
  scoped essential hypotheses is bidirectionally equivalent to the source
  theorem context. The result remains internally universally quantified over
  every integer word, and the explicit + 0 premise and all VC conjuncts are
  retained. The unused digit and num carriers do not occur in the verification
  condition and are conservatively omitted. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c NTP4VCValue NTP4VCValid $.

ntp4vc-value-syntax $a class ( NTP4VCValue A B ) $.
ntp4vc-valid-syntax $a wff ( NTP4VCValid A B ) $.

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

${
  $d r A B C $.

  $( Source parameters: A=base, B=n1, and C=n2. $)

  ntp4vc-base-integer $e |- A e. ZZ $.
  ntp4vc-base-lower-bound $e |- 1 < A $.
  ntp4vc-n1-list $e |- B e. Word ZZ $.
  ntp4vc-n2-list $e |- C e. Word ZZ $.

  ntp4vc-n1-valid $e |- ( NTP4VCValid A B ) $.
  ntp4vc-n2-valid $e |- ( NTP4VCValid A C ) $.

  ntp4vc-pearl-bignum-add-vc $a |- (
    ( NTP4VCValid A B )
    /\
    (
      ( NTP4VCValid A C )
      /\
      (
        0 <_ 0
        /\
        (
          0 <_ 1
          /\
          A. r e. Word ZZ
            (
              (
                ( NTP4VCValid A r )
                /\
                (
                  ( NTP4VCValue A r )
                  =
                  (
                    (
                      ( NTP4VCValue A B )
                      +
                      ( NTP4VCValue A C )
                    )
                    +
                    0
                  )
                )
              )
              ->
              (
                ( NTP4VCValid A r )
                /\
                (
                  ( NTP4VCValue A r )
                  =
                  (
                    ( NTP4VCValue A B )
                    +
                    ( NTP4VCValue A C )
                  )
                )
              )
            )
        )
      )
    )
  ) $.
$}
