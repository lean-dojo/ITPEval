$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_base_power_of_two_pqtvc:
  the verification condition for recognizing powers of two from 2 through
  256 and returning their exponents in a 32-bit word. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  A 64- or 32-bit word is represented exactly by its unsigned value in the
  complete interval from zero through 2^64-1 or 2^32-1. Booleans are exactly
  the two-element carrier 2, with false = 0 and true = 1.

  NTP4VCRecognition is the pair of source implications connecting a Boolean
  comparison result with equality to the tested word. NTP4VCStage2 through
  NTP4VCStage8 preserve the seven branch-local existential Boolean witnesses
  and their original nested scopes. Each proposition-valued conditional is
  expanded into its equivalent exhaustive true and false guarded cases.
  NTP4VCInitial is fact4, and NTP4VCConclusion is the complete four-conjunct
  postcondition, including the universal quantifier over all nonnegative
  integer exponents.

  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCRecognition
  NTP4VCStage2 NTP4VCStage3 NTP4VCStage4 NTP4VCStage5
  NTP4VCStage6 NTP4VCStage7 NTP4VCStage8
  NTP4VCInitial NTP4VCConclusion
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-recognition-syntax $a wff ( NTP4VCRecognition A B C ) $.
ntp4vc-stage2-syntax $a wff ( NTP4VCStage2 A B ) $.
ntp4vc-stage3-syntax $a wff ( NTP4VCStage3 A B ) $.
ntp4vc-stage4-syntax $a wff ( NTP4VCStage4 A B ) $.
ntp4vc-stage5-syntax $a wff ( NTP4VCStage5 A B ) $.
ntp4vc-stage6-syntax $a wff ( NTP4VCStage6 A B ) $.
ntp4vc-stage7-syntax $a wff ( NTP4VCStage7 A B ) $.
ntp4vc-stage8-syntax $a wff ( NTP4VCStage8 A B ) $.
ntp4vc-initial-syntax $a wff ( NTP4VCInitial A B C ) $.
ntp4vc-conclusion-syntax $a wff ( NTP4VCConclusion A B ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-recognition-definition $a |- (
  NTP4VCRecognition A B C
) <-> (
  ( A = C -> B = 1 )
  /\
  ( B = 1 -> A = C )
) $.

${
  $d t A $.  $d t B $.

  ntp4vc-stage8-definition $a |- (
    NTP4VCStage8 A B
  ) <-> (
    E. t e. { 0 , 1 }
      (
        ( NTP4VCRecognition A t ; 2 5 6 )
        /\
        (
          ( t = 1 /\ B = 8 )
          \/
          ( t =/= 1 /\ B = 0 )
        )
      )
  ) $.
$}

${
  $d s A $.  $d s B $.

  ntp4vc-stage7-definition $a |- (
    NTP4VCStage7 A B
  ) <-> (
    E. s e. { 0 , 1 }
      (
        ( NTP4VCRecognition A s ; 1 2 8 )
        /\
        (
          ( s = 1 /\ B = 7 )
          \/
          ( s =/= 1 /\ NTP4VCStage8 A B )
        )
      )
  ) $.
$}

${
  $d r A $.  $d r B $.

  ntp4vc-stage6-definition $a |- (
    NTP4VCStage6 A B
  ) <-> (
    E. r e. { 0 , 1 }
      (
        ( NTP4VCRecognition A r ; 6 4 )
        /\
        (
          ( r = 1 /\ B = 6 )
          \/
          ( r =/= 1 /\ NTP4VCStage7 A B )
        )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.

  ntp4vc-stage5-definition $a |- (
    NTP4VCStage5 A B
  ) <-> (
    E. q e. { 0 , 1 }
      (
        ( NTP4VCRecognition A q ; 3 2 )
        /\
        (
          ( q = 1 /\ B = 5 )
          \/
          ( q =/= 1 /\ NTP4VCStage6 A B )
        )
      )
  ) $.
$}

${
  $d p A $.  $d p B $.

  ntp4vc-stage4-definition $a |- (
    NTP4VCStage4 A B
  ) <-> (
    E. p e. { 0 , 1 }
      (
        ( NTP4VCRecognition A p ; 1 6 )
        /\
        (
          ( p = 1 /\ B = 4 )
          \/
          ( p =/= 1 /\ NTP4VCStage5 A B )
        )
      )
  ) $.
$}

${
  $d o A $.  $d o B $.

  ntp4vc-stage3-definition $a |- (
    NTP4VCStage3 A B
  ) <-> (
    E. o e. { 0 , 1 }
      (
        ( NTP4VCRecognition A o 8 )
        /\
        (
          ( o = 1 /\ B = 3 )
          \/
          ( o =/= 1 /\ NTP4VCStage4 A B )
        )
      )
  ) $.
$}

${
  $d m A $.  $d m B $.

  ntp4vc-stage2-definition $a |- (
    NTP4VCStage2 A B
  ) <-> (
    E. m e. { 0 , 1 }
      (
        ( NTP4VCRecognition A m 4 )
        /\
        (
          ( m = 1 /\ B = 2 )
          \/
          ( m =/= 1 /\ NTP4VCStage3 A B )
        )
      )
  ) $.
$}

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A B C
) <-> (
  ( B = 1 /\ C = 1 )
  \/
  ( B =/= 1 /\ NTP4VCStage2 A C )
) $.

${
  $d n A $.  $d n B $.

  ntp4vc-conclusion-definition $a |- (
    NTP4VCConclusion A B
  ) <-> (
    (
      0 <_ B
      /\
      B <_ 8
    )
    /\
    (
      (
        B =/= 0
        ->
        ( 2 ^ B ) = A
      )
      /\
      (
        B = 0
        ->
        A. n e. ZZ
          (
            0 <_ n
            ->
            ( 2 ^ n ) =/= A
          )
      )
    )
  ) $.
$}

${
  $( Source theorem parameters A=b, B=o1, and C=result. $)
  ntp4vc-b-word64 $e |- A e. NTP4VCWord64 $.
  ntp4vc-o1-boolean $e |- B e. { 0 , 1 } $.
  ntp4vc-result-word32 $e |- C e. NTP4VCWord32 $.

  ntp4vc-fact0 $e |- 2 <_ A $.
  ntp4vc-fact1 $e |- A <_ ; 2 5 6 $.
  ntp4vc-fact2 $e |- ( A = 2 -> B = 1 ) $.
  ntp4vc-fact3 $e |- ( B = 1 -> A = 2 ) $.
  ntp4vc-fact4 $e |- ( NTP4VCInitial A B C ) $.

  ntp4vc-pearl-multiprecision-base-info-power-of-two-vc $a |- (
    NTP4VCConclusion A C
  ) $.
$}
