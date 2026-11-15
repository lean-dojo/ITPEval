$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bitcount_BitCounting32_countqtvc: the 32-bit population-count
  verification condition records five fixed-width bit-manipulation stages
  and conditionally identifies the masked result with the number of set bits.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A source 32-bit word is represented exactly by its unsigned value from zero
  through 2^32-1. NTP4VCBit32 is binary digit extraction. Fixed-width
  addition and subtraction are integer operations modulo 2^32, logical right
  shift is division by a power of two followed by floor, and NTP4VCAnd32
  reconstructs bitwise conjunction from all 32 binary digits.

  NTP4VCCount32 is the sum of the 32 digits, exactly the source numof over
  indices 0 through 31 after expanding nth_closure_def. The five stage
  functions name the source theorem's repeated let-expanded expressions;
  their corresponding step predicates reproduce step0 through step4.
  Unsigned conversion is the identity on NTP4VCWord32, and CountLogic32 is
  definitionally the same population count as the source count_logic.

  Naming the repeated stage expressions is a definitional compression only:
  expanding Stage1 through Stage5 yields the source expressions verbatim.
  The arbitrary input retains the complete 32-bit carrier, every source
  conjunct remains explicit, and the final implication retains its original
  antecedent and conclusion. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCWord32 NTP4VCBit32 NTP4VCShiftR32 NTP4VCAnd32
  NTP4VCAdd32 NTP4VCSub32 NTP4VCCount32 NTP4VCCountLogic32
  NTP4VCStage1 NTP4VCStage2 NTP4VCStage3 NTP4VCStage4 NTP4VCStage5
  NTP4VCStep0 NTP4VCStep1 NTP4VCStep2 NTP4VCStep3 NTP4VCStep4
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-bit32-syntax $a class ( NTP4VCBit32 A B ) $.
ntp4vc-shiftr32-syntax $a class ( NTP4VCShiftR32 A B ) $.
ntp4vc-and32-syntax $a class ( NTP4VCAnd32 A B ) $.
ntp4vc-add32-syntax $a class ( NTP4VCAdd32 A B ) $.
ntp4vc-sub32-syntax $a class ( NTP4VCSub32 A B ) $.
ntp4vc-count32-syntax $a class ( NTP4VCCount32 A ) $.
ntp4vc-count-logic32-syntax $a class ( NTP4VCCountLogic32 A ) $.
ntp4vc-stage1-syntax $a class ( NTP4VCStage1 A ) $.
ntp4vc-stage2-syntax $a class ( NTP4VCStage2 A ) $.
ntp4vc-stage3-syntax $a class ( NTP4VCStage3 A ) $.
ntp4vc-stage4-syntax $a class ( NTP4VCStage4 A ) $.
ntp4vc-stage5-syntax $a class ( NTP4VCStage5 A ) $.
ntp4vc-step0-syntax $a wff ( NTP4VCStep0 A B ) $.
ntp4vc-step1-syntax $a wff ( NTP4VCStep1 A B ) $.
ntp4vc-step2-syntax $a wff ( NTP4VCStep2 A B ) $.
ntp4vc-step3-syntax $a wff ( NTP4VCStep3 A B ) $.
ntp4vc-step4-syntax $a wff ( NTP4VCStep4 A B ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-bit32-definition $a |- ( NTP4VCBit32 A B ) =
  ( ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2 ) $.

ntp4vc-shiftr32-definition $a |- ( NTP4VCShiftR32 A B ) =
  ( |_ ` ( A / ( 2 ^ B ) ) ) $.

${
  $d k A $.  $d k B $.

  ntp4vc-and32-definition $a |- ( NTP4VCAnd32 A B ) =
    sum_ k e. ( 0 ... ; 3 1 )
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

ntp4vc-add32-definition $a |- ( NTP4VCAdd32 A B ) =
  ( ( A + B ) mod ( 2 ^ ; 3 2 ) ) $.

ntp4vc-sub32-definition $a |- ( NTP4VCSub32 A B ) =
  ( ( A - B ) mod ( 2 ^ ; 3 2 ) ) $.

${
  $d k A $.

  ntp4vc-count32-definition $a |- ( NTP4VCCount32 A ) =
    sum_ k e. ( 0 ... ; 3 1 ) ( NTP4VCBit32 A k ) $.
$}

ntp4vc-count-logic32-definition $a |- ( NTP4VCCountLogic32 A ) =
  ( NTP4VCCount32 A ) $.

ntp4vc-stage1-definition $a |- ( NTP4VCStage1 A ) =
  (
    NTP4VCSub32
      A
      (
        NTP4VCAnd32
          ( NTP4VCShiftR32 A 1 )
          ; 1 4 3 1 6 5 5 7 6 5
      )
  ) $.

ntp4vc-stage2-definition $a |- ( NTP4VCStage2 A ) =
  (
    NTP4VCAdd32
      (
        NTP4VCAnd32
          ( NTP4VCStage1 A )
          ; 8 5 8 9 9 3 4 5 9
      )
      (
        NTP4VCAnd32
          ( NTP4VCShiftR32 ( NTP4VCStage1 A ) 2 )
          ; 8 5 8 9 9 3 4 5 9
      )
  ) $.

ntp4vc-stage3-definition $a |- ( NTP4VCStage3 A ) =
  (
    NTP4VCAnd32
      (
        NTP4VCAdd32
          ( NTP4VCStage2 A )
          ( NTP4VCShiftR32 ( NTP4VCStage2 A ) 4 )
      )
      ; 2 5 2 6 4 5 1 3 5
  ) $.

ntp4vc-stage4-definition $a |- ( NTP4VCStage4 A ) =
  (
    NTP4VCAdd32
      ( NTP4VCStage3 A )
      ( NTP4VCShiftR32 ( NTP4VCStage3 A ) 8 )
  ) $.

ntp4vc-stage5-definition $a |- ( NTP4VCStage5 A ) =
  (
    NTP4VCAdd32
      ( NTP4VCStage4 A )
      ( NTP4VCShiftR32 ( NTP4VCStage4 A ) ; 1 6 )
  ) $.

ntp4vc-step0-definition $a |- (
  NTP4VCStep0 A B
) <-> (
  B = ( NTP4VCStage1 A )
) $.

ntp4vc-step1-definition $a |- (
  NTP4VCStep1 A B
) <-> (
  B = (
    NTP4VCAdd32
      ( NTP4VCAnd32 A ; 8 5 8 9 9 3 4 5 9 )
      (
        NTP4VCAnd32
          ( NTP4VCShiftR32 A 2 )
          ; 8 5 8 9 9 3 4 5 9
      )
  )
) $.

ntp4vc-step2-definition $a |- (
  NTP4VCStep2 A B
) <-> (
  B = (
    NTP4VCAnd32
      ( NTP4VCAdd32 A ( NTP4VCShiftR32 A 4 ) )
      ; 2 5 2 6 4 5 1 3 5
  )
) $.

ntp4vc-step3-definition $a |- (
  NTP4VCStep3 A B
) <-> (
  B = (
    NTP4VCAdd32 A ( NTP4VCShiftR32 A 8 )
  )
) $.

ntp4vc-step4-definition $a |- (
  NTP4VCStep4 A B
) <-> (
  B = (
    NTP4VCAdd32 A ( NTP4VCShiftR32 A ; 1 6 )
  )
) $.

${
  $( Source theorem parameter A=n. $)
  ntp4vc-n-word32 $e |- A e. NTP4VCWord32 $.

  ntp4vc-pearl-bitcount-count-vc $a |- (
    ( NTP4VCStep0 A ( NTP4VCStage1 A ) )
    /\
    (
      ( NTP4VCStep1 ( NTP4VCStage1 A ) ( NTP4VCStage2 A ) )
      /\
      (
        ( NTP4VCStep2 ( NTP4VCStage2 A ) ( NTP4VCStage3 A ) )
        /\
        (
          ( NTP4VCStep3 ( NTP4VCStage3 A ) ( NTP4VCStage4 A ) )
          /\
          (
            ( NTP4VCStep4 ( NTP4VCStage4 A ) ( NTP4VCStage5 A ) )
            /\
            (
              (
                NTP4VCAnd32
                  ( NTP4VCStage5 A )
                  ; 6 3
              ) = ( NTP4VCCount32 A )
              ->
              (
                NTP4VCAnd32
                  ( NTP4VCStage5 A )
                  ; 6 3
              ) = ( NTP4VCCountLogic32 A )
            )
          )
        )
      )
    )
  ) $.
$}
