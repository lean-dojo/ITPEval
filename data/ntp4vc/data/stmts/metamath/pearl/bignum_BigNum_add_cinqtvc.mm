$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bignum_BigNum_add_cinqtvc: the big-number addition verification
  condition states the validity and numerical-value obligations for adding
  two little-endian base-b integer lists with a carry bit. This file contains
  no proof.
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
  existential recursive result remains internally quantified over every
  integer word. Splitting the base declaration and theorem parameters and
  assumptions into scoped essential hypotheses is bidirectionally equivalent
  to the source theorem context. The unused digit and num carriers are
  conservatively extendible and do not alter this proposition. The final
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
ntp4vc-first-syntax $a wff ( NTP4VCFirst A B C D ) $.
ntp4vc-premise-syntax
  $a wff ( NTP4VCPremise A B C D E ) $.

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
  NTP4VCFirst A B C D
) <-> (
  (
    ( # ` C ) = 0
    /\
    (
      (
        ( # ` B ) = 0
        /\
        (
          ( NTP4VCValid A C )
          /\
          (
            0 <_ D
            /\
            D < A
          )
        )
      )
      \/
      (
        0 < ( # ` B )
        /\
        (
          ( NTP4VCValid A B )
          /\
          (
            0 <_ D
            /\
            D < A
          )
        )
      )
    )
  )
  \/
  (
    0 < ( # ` C )
    /\
    (
      (
        ( # ` B ) = 0
        /\
        (
          ( NTP4VCValid A C )
          /\
          (
            0 <_ D
            /\
            D < A
          )
        )
      )
      \/
      (
        0 < ( # ` B )
        /\
        (
          (
            ( ( D + ( B ` 0 ) ) + ( C ` 0 ) ) < A
            /\
            (
              ( NTP4VCTail B ) = ( NTP4VCTail B )
              /\
              (
                ( NTP4VCValid A ( NTP4VCTail B ) )
                /\
                (
                  ( NTP4VCValid A ( NTP4VCTail C ) )
                  /\
                  (
                    0 <_ 0
                    /\
                    0 <_ 1
                  )
                )
              )
            )
          )
          \/
          (
            -. ( ( ( D + ( B ` 0 ) ) + ( C ` 0 ) ) < A )
            /\
            (
              ( NTP4VCTail B ) = ( NTP4VCTail B )
              /\
              (
                ( NTP4VCValid A ( NTP4VCTail B ) )
                /\
                (
                  ( NTP4VCValid A ( NTP4VCTail C ) )
                  /\
                  (
                    0 <_ 1
                    /\
                    1 <_ 1
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

${
  $d o A B C D E $.

  ntp4vc-premise-definition $a |- (
    NTP4VCPremise A B C D E
  ) <-> (
    (
      ( # ` C ) = 0
      /\
      (
        (
          ( # ` B ) = 0
          /\
          (
            ( NTP4VCValid A E )
            /\
            (
              ( NTP4VCValue A E )
              =
              ( ( NTP4VCValue A C ) + D )
            )
          )
        )
        \/
        (
          0 < ( # ` B )
          /\
          (
            ( NTP4VCValid A E )
            /\
            (
              ( NTP4VCValue A E )
              =
              ( ( NTP4VCValue A B ) + D )
            )
          )
        )
      )
    )
    \/
    (
      0 < ( # ` C )
      /\
      (
        (
          ( # ` B ) = 0
          /\
          (
            ( NTP4VCValid A E )
            /\
            (
              ( NTP4VCValue A E )
              =
              ( ( NTP4VCValue A C ) + D )
            )
          )
        )
        \/
        (
          0 < ( # ` B )
          /\
          (
            (
              ( ( D + ( B ` 0 ) ) + ( C ` 0 ) ) < A
              /\
              E. o e. Word ZZ
                (
                  (
                    ( NTP4VCValid A o )
                    /\
                    (
                      ( NTP4VCValue A o )
                      =
                      (
                        (
                          ( NTP4VCValue A ( NTP4VCTail B ) )
                          +
                          ( NTP4VCValue A ( NTP4VCTail C ) )
                        )
                        +
                        0
                      )
                    )
                  )
                  /\
                  E = (
                    <" ( ( D + ( B ` 0 ) ) + ( C ` 0 ) ) ">
                    ++
                    o
                  )
                )
            )
            \/
            (
              -. ( ( ( D + ( B ` 0 ) ) + ( C ` 0 ) ) < A )
              /\
              E. o e. Word ZZ
                (
                  (
                    ( NTP4VCValid A o )
                    /\
                    (
                      ( NTP4VCValue A o )
                      =
                      (
                        (
                          ( NTP4VCValue A ( NTP4VCTail B ) )
                          +
                          ( NTP4VCValue A ( NTP4VCTail C ) )
                        )
                        +
                        1
                      )
                    )
                  )
                  /\
                  E = (
                    <"
                      (
                        ( ( D + ( B ` 0 ) ) + ( C ` 0 ) )
                        -
                        A
                      )
                    ">
                    ++
                    o
                  )
                )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d r A B C D $.

  $( Source parameters: A=base, B=n1, C=n2, and D=cin. $)

  ntp4vc-base-integer $e |- A e. ZZ $.
  ntp4vc-base-lower-bound $e |- 1 < A $.
  ntp4vc-n1-list $e |- B e. Word ZZ $.
  ntp4vc-n2-list $e |- C e. Word ZZ $.
  ntp4vc-cin-integer $e |- D e. ZZ $.

  ntp4vc-n1-valid $e |- ( NTP4VCValid A B ) $.
  ntp4vc-n2-valid $e |- ( NTP4VCValid A C ) $.
  ntp4vc-cin-nonnegative $e |- 0 <_ D $.
  ntp4vc-cin-at-most-one $e |- D <_ 1 $.

  ntp4vc-pearl-bignum-add-cin-vc $a |- (
    ( NTP4VCFirst A B C D )
    /\
    A. r e. Word ZZ
      (
        ( NTP4VCPremise A B C D r )
        ->
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
              D
            )
          )
        )
      )
  ) $.
$}
