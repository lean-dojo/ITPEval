$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_win_sizeqtvc: the signed 32-bit
  modular-exponentiation window-size threshold cascade, its result bounds
  from zero through ten, and positivity for positive inputs. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A source 32-bit word is represented exactly by its unsigned integer value
  from zero through 2^32-1. NTP4VCSigned32 is the standard two's-complement
  bijection from that carrier to the signed integers from -2^31 through
  2^31-1. The source Boolean carrier is the explicit two-element set {0, 1},
  with false represented by 0 and true by 1.

  NTP4VCWindowChoice is the source nested conditional verbatim after those
  exact representations are expanded. In the scoped statement, A, B, and C
  are respectively eb, o1, and result. The three essential hypotheses are
  precisely fact0, fact1, and fact2; the conclusion retains the original
  conjunction and positivity implication. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains
  no $p proof declaration.
$)

$c NTP4VCWord32 NTP4VCSigned32 NTP4VCWindowChoice $.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-window-choice-syntax
  $a class ( NTP4VCWindowChoice A B ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-signed32-definition $a |- ( NTP4VCSigned32 A ) =
  if (
    A < ( 2 ^ ; 3 1 ) ,
    A ,
    ( A - ( 2 ^ ; 3 2 ) )
  ) $.

ntp4vc-window-choice-definition $a |- (
  NTP4VCWindowChoice A B
) = if (
  B = 1 ,
  0 ,
  if (
    ( NTP4VCSigned32 A ) <_ 7 ,
    1 ,
    if (
      ( NTP4VCSigned32 A ) <_ ; 2 5 ,
      2 ,
      if (
        ( NTP4VCSigned32 A ) <_ ; 8 1 ,
        3 ,
        if (
          ( NTP4VCSigned32 A ) <_ ; ; 2 1 4 ,
          4 ,
          if (
            ( NTP4VCSigned32 A ) <_ ; ; 6 7 3 ,
            5 ,
            if (
              ( NTP4VCSigned32 A ) <_ ; ; ; 1 7 9 3 ,
              6 ,
              if (
                ( NTP4VCSigned32 A ) <_ ; ; ; 4 6 0 9 ,
                7 ,
                if (
                  ( NTP4VCSigned32 A ) <_ ; ; ; ; 1 1 5 2 1 ,
                  8 ,
                  if (
                    ( NTP4VCSigned32 A ) <_ ; ; ; ; 2 8 1 6 1 ,
                    9 ,
                    ; 1 0
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
  $( Source parameters A=eb, B=o1, C=result and assumptions fact0--fact2. $)
  ntp4vc-eb-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-o1-bool $e |- B e. { 0 , 1 } $.
  ntp4vc-result-word32 $e |- C e. NTP4VCWord32 $.
  ntp4vc-fact0 $e |- (
    ( NTP4VCSigned32 A ) = ( NTP4VCSigned32 0 )
    ->
    B = 1
  ) $.
  ntp4vc-fact1 $e |- (
    B = 1
    ->
    A = 0
  ) $.
  ntp4vc-fact2 $e |- C = ( NTP4VCWindowChoice A B ) $.

  ntp4vc-pearl-multiprecision-powm-win-size-vc $a |- (
    0 <_ ( NTP4VCSigned32 C )
    /\
    (
      ( NTP4VCSigned32 C ) <_ ; 1 0
      /\
      (
        0 < ( NTP4VCSigned32 A )
        ->
        0 < ( NTP4VCSigned32 C )
      )
    )
  ) $.
$}
