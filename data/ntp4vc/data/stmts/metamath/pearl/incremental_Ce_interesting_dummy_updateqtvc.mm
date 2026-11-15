$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/incremental_Ce_interesting_dummy_updateqtvc: the incremental signed
  32-bit dummy-update verification condition assumes an input signed value
  above 22 and specifies signed bounds for 42 and its double, followed by a
  nested output upper bound of 42. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A 32-bit word is represented exactly by its unsigned integer value from
  zero through 2^32-1. NTP4VCSigned32 is the standard two's-complement
  bijection from that carrier to the signed integers from -2^31 through
  2^31-1. NTP4VCInt32InBounds is the source signed-32 bounds predicate.

  In the scoped statement, A is the source word r, while x and y are the
  universally quantified source words o1 and o2. The essential hypotheses
  are the typed parameter r and the assumption that its signed value exceeds
  22. Expanding the two definitions recovers the complete source conjunction
  and both nested implications without changing any word or integer domain.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p declaration.
$)

$c NTP4VCWord32 NTP4VCSigned32 NTP4VCInt32InBounds $.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syntax
  $a wff ( NTP4VCInt32InBounds A ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-signed32-definition $a |- ( NTP4VCSigned32 A ) =
  if (
    A < ( 2 ^ ; 3 1 ) ,
    A ,
    ( A - ( 2 ^ ; 3 2 ) )
  ) $.

ntp4vc-int32-in-bounds-definition $a |- (
  NTP4VCInt32InBounds A
) <-> (
  A e. ZZ
  /\
  (
    ( -u ( 2 ^ ; 3 1 ) ) <_ A
    /\
    A < ( 2 ^ ; 3 1 )
  )
) $.

${
  $d x A $.  $d y A $.  $d x y $.

  $( Source parameter A=r and assumption fact0. $)
  ntp4vc-r-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-fact0 $e |- ; 2 2 < ( NTP4VCSigned32 A ) $.

  ntp4vc-pearl-incremental-ce-interesting-dummy-update-vc $a |- (
    ( NTP4VCInt32InBounds ; 4 2 )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x ) = ; 4 2
        ->
        (
          (
            NTP4VCInt32InBounds
              (
                ( NTP4VCSigned32 x )
                +
                ( NTP4VCSigned32 x )
              )
          )
          /\
          A. y e. NTP4VCWord32
            (
              (
                NTP4VCSigned32 y
              ) = (
                ( NTP4VCSigned32 x )
                +
                ( NTP4VCSigned32 x )
              )
              ->
              ( NTP4VCSigned32 y ) <_ ; 4 2
            )
        )
      )
  ) $.
$}
