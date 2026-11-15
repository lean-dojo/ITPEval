$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/gcd_vc_sp_BinaryGcd_binary_gcdqtvc: the binary-gcd verification
  condition states recursive-call descent obligations and preservation of the
  integer greatest common divisor for nonnegative inputs. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and its built-in gcd
  operator is the canonical nonnegative greatest common divisor on integers.
  NTP4VCTDiv2 is integer division by 2 truncated toward zero, and
  NTP4VCTMod2 is its associated remainder. These are exactly the
  ComputerDivision quotient and remainder operations imported by the pinned
  Why3 mach.int.Int source.

  NTP4VCDescent expands every proposition-valued conditional in the selected
  Why3 binary_gcd verification condition into an exhaustive guarded
  disjunction and substitutes all let-bound halves. NTP4VCResultValue
  preserves the term-valued conditional selecting the recursive result.
  Splitting the integer parameters and their nonnegativity assumptions into
  scoped essential hypotheses is bidirectionally equivalent to the original
  generated VC, and the result quantifier retains its full integer domain.

  The official Rocq source reverses quotient and remainder in the parity tests
  and recursive arguments. Under the canonical resolution it is a secondary
  export defect and does not override the pinned original Why3 goal; the Lean
  and Isabelle exports preserve the original operation placement. The final
  declaration is Metamath's native unproved $a statement encoding, and this
  database contains no artifact-level $p proof.
$)

$c
  NTP4VCTDiv2 NTP4VCTMod2 NTP4VCDescent NTP4VCResultValue
$.

ntp4vc-tdiv2-syntax $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-tmod2-syntax $a class ( NTP4VCTMod2 A ) $.
ntp4vc-descent-syntax $a wff ( NTP4VCDescent A B ) $.
ntp4vc-result-value-syntax $a class ( NTP4VCResultValue A B ) $.

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

ntp4vc-tmod2-definition $a |- (
  NTP4VCTMod2 A
) = (
  A - ( 2 x. ( NTP4VCTDiv2 A ) )
) $.

ntp4vc-descent-definition $a |- (
  ( NTP4VCDescent A B )
  <->
  (
    (
      A < B
      /\
      (
        (
          (
            0 <_ B
            /\
            A < B
          )
          \/
          (
            B = A
            /\
            (
              0 <_ A
              /\
              B < A
            )
          )
        )
        /\
        (
          0 <_ B
          /\
          0 <_ A
        )
      )
    )
    \/
    (
      -. A < B
      /\
      (
        B =/= 0
        ->
        (
          2 =/= 0
          /\
          (
            (
              ( NTP4VCTMod2 A ) = 0
              /\
              (
                2 =/= 0
                /\
                (
                  (
                    ( NTP4VCTMod2 B ) = 0
                    /\
                    (
                      2 =/= 0
                      /\
                      (
                        2 =/= 0
                        /\
                        (
                          (
                            (
                              0 <_ B
                              /\
                              ( NTP4VCTDiv2 B ) < B
                            )
                            \/
                            (
                              B = ( NTP4VCTDiv2 B )
                              /\
                              (
                                0 <_ A
                                /\
                                ( NTP4VCTDiv2 A ) < A
                              )
                            )
                          )
                          /\
                          (
                            0 <_ ( NTP4VCTDiv2 A )
                            /\
                            0 <_ ( NTP4VCTDiv2 B )
                          )
                        )
                      )
                    )
                  )
                  \/
                  (
                    ( NTP4VCTMod2 B ) =/= 0
                    /\
                    (
                      2 =/= 0
                      /\
                      (
                        (
                          0 <_ A
                          /\
                          ( NTP4VCTDiv2 A ) < A
                        )
                        /\
                        (
                          0 <_ ( NTP4VCTDiv2 A )
                          /\
                          0 <_ B
                        )
                      )
                    )
                  )
                )
              )
            )
            \/
            (
              ( NTP4VCTMod2 A ) =/= 0
              /\
              (
                2 =/= 0
                /\
                (
                  (
                    ( NTP4VCTMod2 B ) = 0
                    /\
                    (
                      2 =/= 0
                      /\
                      (
                        (
                          0 <_ B
                          /\
                          ( NTP4VCTDiv2 B ) < B
                        )
                        /\
                        (
                          0 <_ A
                          /\
                          0 <_ ( NTP4VCTDiv2 B )
                        )
                      )
                    )
                  )
                  \/
                  (
                    ( NTP4VCTMod2 B ) =/= 0
                    /\
                    (
                      2 =/= 0
                      /\
                      (
                        (
                          0 <_ A
                          /\
                          ( NTP4VCTDiv2 ( A - B ) ) < A
                        )
                        /\
                        (
                          0 <_ ( NTP4VCTDiv2 ( A - B ) )
                          /\
                          0 <_ B
                        )
                      )
                    )
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

ntp4vc-result-value-definition $a |- (
  NTP4VCResultValue A B
) = if (
  A < B ,
  ( B gcd A ) ,
  if (
    B = 0 ,
    A ,
    if (
      ( NTP4VCTMod2 A ) = 0 ,
      if (
        ( NTP4VCTMod2 B ) = 0 ,
        ( 2 x. ( ( NTP4VCTDiv2 A ) gcd ( NTP4VCTDiv2 B ) ) ) ,
        ( ( NTP4VCTDiv2 A ) gcd B )
      ) ,
      if (
        ( NTP4VCTMod2 B ) = 0 ,
        ( A gcd ( NTP4VCTDiv2 B ) ) ,
        ( ( NTP4VCTDiv2 ( A - B ) ) gcd B )
      )
    )
  )
) $.

${
  $d r A B $.

  $( Source parameters: A=u and B=v. $)

  ntp4vc-u-integer $e |- A e. ZZ $.
  ntp4vc-v-integer $e |- B e. ZZ $.

  ntp4vc-u-nonnegative $e |- 0 <_ A $.
  ntp4vc-v-nonnegative $e |- 0 <_ B $.

  ntp4vc-pearl-gcd-vc-sp-binary-gcd-vc $a |- (
    ( NTP4VCDescent A B )
    /\
    A. r e. ZZ
      (
        r = ( NTP4VCResultValue A B )
        ->
        r = ( A gcd B )
      )
  ) $.
$}
