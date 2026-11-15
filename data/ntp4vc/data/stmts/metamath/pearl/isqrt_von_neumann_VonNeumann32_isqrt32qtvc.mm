$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/isqrt_von_neumann_VonNeumann32_isqrt32qtvc: the 32-bit Von Neumann
  integer-square-root verification condition establishes the initial
  square bounds and preserves them across the guarded bitwise loop step.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A source 32-bit word is represented exactly by its unsigned value from zero
  through 2^32-1. Addition, subtraction, and multiplication are integer
  operations modulo 2^32. Logical shifts use the unsigned shift count and
  return zero when that count is at least 32. NTP4VCAnd32 and NTP4VCOr32
  reconstruct bitwise conjunction and disjunction from all 32 binary digits.
  Thus these definitions give the complete source BitVec 32 carrier and its
  unsigned operations, rather than a bounded sample of possible states.

  NTP4VCPrevPow is the source conditional power-of-two term,
  NTP4VCTrial is its let-bound value b, and NTP4VCCommon,
  NTP4VCAddCase, NTP4VCKeepCase, and NTP4VCTerminal name the three loop
  branches and their shared conjuncts. NTP4VCTransition expands both
  proposition-valued source conditionals into exhaustive guarded
  disjunctions. Expanding these definitions recovers every source equality,
  unsigned comparison, modular operation, assumption, and conclusion.

  The scoped essential hypothesis represents the arbitrary source input x,
  while res_g, m, and num retain universal quantification over the complete
  32-bit carrier. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCWord32 NTP4VCBit32
  NTP4VCAdd32 NTP4VCSub32 NTP4VCMul32
  NTP4VCShiftL32 NTP4VCShiftR32 NTP4VCAnd32 NTP4VCOr32
  NTP4VCSqr NTP4VCIsPow2 NTP4VCPrevPow NTP4VCScale NTP4VCTrial
  NTP4VCCommon NTP4VCAddCase NTP4VCKeepCase NTP4VCTerminal
  NTP4VCTransition NTP4VCStep NTP4VCInitial
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-bit32-syntax $a class ( NTP4VCBit32 A B ) $.
ntp4vc-add32-syntax $a class ( NTP4VCAdd32 A B ) $.
ntp4vc-sub32-syntax $a class ( NTP4VCSub32 A B ) $.
ntp4vc-mul32-syntax $a class ( NTP4VCMul32 A B ) $.
ntp4vc-shiftl32-syntax $a class ( NTP4VCShiftL32 A B ) $.
ntp4vc-shiftr32-syntax $a class ( NTP4VCShiftR32 A B ) $.
ntp4vc-and32-syntax $a class ( NTP4VCAnd32 A B ) $.
ntp4vc-or32-syntax $a class ( NTP4VCOr32 A B ) $.
ntp4vc-sqr-syntax $a class ( NTP4VCSqr A ) $.
ntp4vc-is-pow2-syntax $a wff ( NTP4VCIsPow2 A B ) $.
ntp4vc-prev-pow-syntax $a class ( NTP4VCPrevPow A ) $.
ntp4vc-scale-syntax $a class ( NTP4VCScale A B ) $.
ntp4vc-trial-syntax $a class ( NTP4VCTrial A B ) $.
ntp4vc-common-syntax $a wff ( NTP4VCCommon A ) $.
ntp4vc-add-case-syntax $a wff ( NTP4VCAddCase A B C D ) $.
ntp4vc-keep-case-syntax $a wff ( NTP4VCKeepCase A B C D ) $.
ntp4vc-terminal-syntax $a wff ( NTP4VCTerminal A B C ) $.
ntp4vc-transition-syntax $a wff ( NTP4VCTransition A B C D ) $.
ntp4vc-step-syntax $a wff ( NTP4VCStep A B C D ) $.
ntp4vc-initial-syntax $a wff ( NTP4VCInitial A ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-bit32-definition $a |- (
  NTP4VCBit32 A B
) = (
  ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2
) $.

ntp4vc-add32-definition $a |- (
  NTP4VCAdd32 A B
) = (
  ( A + B ) mod ( 2 ^ ; 3 2 )
) $.

ntp4vc-sub32-definition $a |- (
  NTP4VCSub32 A B
) = (
  ( A - B ) mod ( 2 ^ ; 3 2 )
) $.

ntp4vc-mul32-definition $a |- (
  NTP4VCMul32 A B
) = (
  ( A x. B ) mod ( 2 ^ ; 3 2 )
) $.

ntp4vc-shiftl32-definition $a |- (
  NTP4VCShiftL32 A B
) = if (
  B < ; 3 2 ,
  ( ( A x. ( 2 ^ B ) ) mod ( 2 ^ ; 3 2 ) ) ,
  0
) $.

ntp4vc-shiftr32-definition $a |- (
  NTP4VCShiftR32 A B
) = if (
  B < ; 3 2 ,
  ( |_ ` ( A / ( 2 ^ B ) ) ) ,
  0
) $.

${
  $d k A $.  $d k B $.

  ntp4vc-and32-definition $a |- (
    NTP4VCAnd32 A B
  ) = sum_ k e. ( 0 ... ; 3 1 )
    if (
      (
        ( ( NTP4VCBit32 A k ) = 1 )
        /\
        ( ( NTP4VCBit32 B k ) = 1 )
      ) ,
      ( 2 ^ k ) ,
      0
    ) $.
$}

${
  $d k A $.  $d k B $.

  ntp4vc-or32-definition $a |- (
    NTP4VCOr32 A B
  ) = sum_ k e. ( 0 ... ; 3 1 )
    if (
      (
        ( ( NTP4VCBit32 A k ) = 1 )
        \/
        ( ( NTP4VCBit32 B k ) = 1 )
      ) ,
      ( 2 ^ k ) ,
      0
    ) $.
$}

ntp4vc-sqr-definition $a |- (
  NTP4VCSqr A
) = (
  NTP4VCMul32 A A
) $.

ntp4vc-is-pow2-definition $a |- (
  NTP4VCIsPow2 A B
) <-> (
  (
    NTP4VCAnd32
      A
      ( NTP4VCSub32 ( NTP4VCShiftL32 1 B ) 1 )
  ) = 0
) $.

ntp4vc-prev-pow-definition $a |- (
  NTP4VCPrevPow A
) = if (
  A = 0 ,
  0 ,
  ( NTP4VCShiftL32 1 ( NTP4VCSub32 A 1 ) )
) $.

ntp4vc-scale-definition $a |- (
  NTP4VCScale A B
) = (
  NTP4VCMul32 A ( NTP4VCShiftL32 1 B )
) $.

ntp4vc-trial-definition $a |- (
  NTP4VCTrial A B
) = (
  NTP4VCOr32
    ( NTP4VCScale A B )
    ( NTP4VCSqr ( NTP4VCPrevPow B ) )
) $.

ntp4vc-common-definition $a |- (
  NTP4VCCommon A
) <-> (
  (
    (
      NTP4VCShiftR32
        ( NTP4VCSqr ( NTP4VCPrevPow A ) )
        2
    )
    <
    ( NTP4VCSqr ( NTP4VCPrevPow A ) )
  )
  /\
  (
    ( NTP4VCSub32 A 1 ) <_ ; 1 6
    /\
    (
      (
        NTP4VCShiftR32
          ( NTP4VCPrevPow A )
          1
      )
      =
      ( NTP4VCPrevPow ( NTP4VCSub32 A 1 ) )
      /\
      (
        NTP4VCShiftR32
          ( NTP4VCSqr ( NTP4VCPrevPow A ) )
          2
      )
      =
      (
        NTP4VCSqr
          ( NTP4VCShiftR32 ( NTP4VCPrevPow A ) 1 )
      )
    )
  )
) $.

ntp4vc-add-case-definition $a |- (
  NTP4VCAddCase A B C D
) <-> (
  ( NTP4VCCommon C )
  /\
  (
    (
      NTP4VCIsPow2
        ( NTP4VCAdd32 B ( NTP4VCPrevPow C ) )
        ( NTP4VCSub32 C 1 )
    )
    /\
    (
      (
        NTP4VCAdd32 B ( NTP4VCPrevPow C )
      ) < ; 6 5 5 3 6
      /\
      (
        (
          NTP4VCOr32
            ( NTP4VCShiftR32 ( NTP4VCScale B C ) 1 )
            ( NTP4VCSqr ( NTP4VCPrevPow C ) )
        )
        =
        (
          NTP4VCMul32
            ( NTP4VCAdd32 B ( NTP4VCPrevPow C ) )
            ( NTP4VCShiftL32 1 ( NTP4VCSub32 C 1 ) )
        )
        /\
        (
          ( NTP4VCSub32 D ( NTP4VCTrial B C ) ) <_ A
          /\
          (
            (
              NTP4VCSub32
                A
                ( NTP4VCSub32 D ( NTP4VCTrial B C ) )
            )
            =
            (
              NTP4VCSqr
                ( NTP4VCAdd32 B ( NTP4VCPrevPow C ) )
            )
            /\
            (
              (
                NTP4VCAdd32
                  ( NTP4VCAdd32 B ( NTP4VCPrevPow C ) )
                  ( NTP4VCShiftL32 1 ( NTP4VCSub32 C 1 ) )
              ) <_ ; 6 5 5 3 6
              /\
              A <_ (
                NTP4VCSub32
                  (
                    NTP4VCSqr
                      (
                        NTP4VCAdd32
                          ( NTP4VCAdd32 B ( NTP4VCPrevPow C ) )
                          (
                            NTP4VCShiftL32
                              1
                              ( NTP4VCSub32 C 1 )
                          )
                      )
                  )
                  1
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-keep-case-definition $a |- (
  NTP4VCKeepCase A B C D
) <-> (
  ( NTP4VCCommon C )
  /\
  (
    ( NTP4VCIsPow2 B ( NTP4VCSub32 C 1 ) )
    /\
    (
      B < ; 6 5 5 3 6
      /\
      (
        (
          NTP4VCShiftR32 ( NTP4VCScale B C ) 1
        )
        =
        (
          NTP4VCMul32
            B
            ( NTP4VCShiftL32 1 ( NTP4VCSub32 C 1 ) )
        )
        /\
        (
          D <_ A
          /\
          (
            ( NTP4VCSub32 A D ) = ( NTP4VCSqr B )
            /\
            (
              (
                NTP4VCAdd32
                  B
                  ( NTP4VCShiftL32 1 ( NTP4VCSub32 C 1 ) )
              ) <_ ; 6 5 5 3 6
              /\
              A <_ (
                NTP4VCSub32
                  (
                    NTP4VCSqr
                      (
                        NTP4VCAdd32
                          B
                          (
                            NTP4VCShiftL32
                              1
                              ( NTP4VCSub32 C 1 )
                          )
                      )
                  )
                  1
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-terminal-definition $a |- (
  NTP4VCTerminal A B C
) <-> (
  (
    NTP4VCSqr ( NTP4VCScale B C )
  ) <_ A
  /\
  A <_ (
    NTP4VCSub32
      (
        NTP4VCSqr
          ( NTP4VCAdd32 ( NTP4VCScale B C ) 1 )
      )
      1
  )
) $.

ntp4vc-transition-definition $a |- (
  NTP4VCTransition A B C D
) <-> (
  (
    (
      -. ( NTP4VCSqr ( NTP4VCPrevPow C ) ) = 0
      /\
      (
        (
          ( NTP4VCTrial B C ) <_ D
          /\
          ( NTP4VCAddCase A B C D )
        )
        \/
        (
          -. ( NTP4VCTrial B C ) <_ D
          /\
          ( NTP4VCKeepCase A B C D )
        )
      )
    )
    \/
    (
      ( NTP4VCSqr ( NTP4VCPrevPow C ) ) = 0
      /\
      ( NTP4VCTerminal A B C )
    )
  )
) $.

ntp4vc-step-definition $a |- (
  NTP4VCStep A B C D
) <-> (
  (
    C <_ ; 1 6
    /\
    (
      ( NTP4VCIsPow2 B C )
      /\
      (
        B < ; 6 5 5 3 6
        /\
        (
          D <_ A
          /\
          (
            ( NTP4VCSub32 A D ) = ( NTP4VCSqr B )
            /\
            (
              (
                NTP4VCAdd32 B ( NTP4VCShiftL32 1 C )
              ) <_ ; 6 5 5 3 6
              /\
              A <_ (
                NTP4VCSub32
                  (
                    NTP4VCSqr
                      ( NTP4VCAdd32 B ( NTP4VCShiftL32 1 C ) )
                  )
                  1
              )
            )
          )
        )
      )
    )
  )
  ->
  ( NTP4VCTransition A B C D )
) $.

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A
) <-> (
  ; 1 6 <_ ; 1 6
  /\
  (
    ; 3 2 7 6 8 = ( NTP4VCPrevPow ; 1 6 )
    /\
    (
      ; 1 0 7 3 7 4 1 8 2 4 = ( NTP4VCSqr ; 3 2 7 6 8 )
      /\
      (
        ( NTP4VCIsPow2 0 ; 1 6 )
        /\
        (
          0 < ; 6 5 5 3 6
          /\
          (
            0 = ( NTP4VCMul32 0 ( NTP4VCShiftL32 1 ; 1 6 ) )
            /\
            (
              A <_ A
              /\
              (
                ( NTP4VCSub32 A A ) = ( NTP4VCSqr 0 )
                /\
                (
                  (
                    NTP4VCAdd32
                      0
                      ( NTP4VCShiftL32 1 ; 1 6 )
                  ) <_ ; 6 5 5 3 6
                  /\
                  A <_ (
                    NTP4VCSub32
                      (
                        NTP4VCSqr
                          (
                            NTP4VCAdd32
                              0
                              ( NTP4VCShiftL32 1 ; 1 6 )
                          )
                      )
                      1
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
  $d r A $.  $d m A $.  $d n A $.
  $d r m $.  $d r n $.  $d m n $.

  $( Source parameter A=x; r=res_g, m=m, and n=num are universal. $)

  ntp4vc-x-word32 $e |- A e. NTP4VCWord32 $.

  ntp4vc-pearl-isqrt-von-neumann32-vc $a |- (
    ( NTP4VCInitial A )
    /\
    A. r e. NTP4VCWord32
      A. m e. NTP4VCWord32
        A. n e. NTP4VCWord32
          ( NTP4VCStep A r m n )
  ) $.
$}
