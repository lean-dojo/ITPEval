$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/__toupper_Why3_ide_VC__toupper_post_goal0: the generated
  toupper verification condition concludes that an unsigned-byte result is
  the uppercase conversion of an unsigned-byte input, under the source
  character-test, conversion, and conditional-update assumptions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The predicates NTP4VCUint8, NTP4VCSint8, and NTP4VCIsLower directly expand
  the source integer definitions. R, S, and T represent to_sint8, to_uint8,
  and l_toupper as arbitrary integer functions. Their displayed laws are
  exactly the relevant imported source axioms: the two conversions have their
  stated ranges and identities, R after S agrees with R, and T subtracts 32
  on lowercase ASCII integers while fixing every other integer. After
  eliminating l_tolower through its uppercase table and non-uppercase
  identity law, the latter piecewise law is bidirectionally equivalent over
  ZZ to the source's toupper inverse and non-lowercase identity axioms.

  The source conditional fact is split into its zero and nonzero implications,
  which is equivalent by classical case analysis. All source integer domains,
  assumptions, and the uppercase equality conclusion are retained. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCSint8Limit NTP4VCUint8Limit
  NTP4VCSint8 NTP4VCUint8 NTP4VCIsLower
$.

ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-is-lower-syntax $a wff ( NTP4VCIsLower A ) $.

ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

ntp4vc-is-lower-def $a |- ( ( NTP4VCIsLower A ) <->
  ( ; 9 7 <_ A /\ A <_ ; 1 2 2 )
) $.

${
  $d x A B C R S T $.

  $( Source parameters A=i_1, B=i, C=i_2. R, S, and T are respectively
     to_sint8, to_uint8, and l_toupper. $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-i-integer $e |- B e. ZZ $.
  ntp4vc-i2-integer $e |- C e. ZZ $.

  ntp4vc-to-sint8-function $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint8-function $e |- S e. ( ZZ ^m ZZ ) $.
  ntp4vc-toupper-function $e |- T e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-sint8-range $e |- A. x e. ZZ
    ( NTP4VCSint8 ( R ` x ) ) $.

  ntp4vc-to-sint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint8 x )
      ->
      ( R ` x ) = x
    ) $.

  ntp4vc-to-uint8-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( S ` x ) ) $.

  ntp4vc-to-uint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
      ->
      ( S ` x ) = x
    ) $.

  ntp4vc-signed-unsigned-projection $e |- A. x e. ZZ
    ( ( R ` ( S ` x ) ) = ( R ` x ) ) $.

  ntp4vc-toupper-character-law $e |- A. x e. ZZ
    (
      (
        ( NTP4VCIsLower x )
        ->
        ( T ` x ) = ( x - ; 3 2 )
      )
      /\
      (
        -. ( NTP4VCIsLower x )
        ->
        ( T ` x ) = x
      )
    ) $.

  ntp4vc-lowercase-test $e |- (
    ( NTP4VCIsLower ( R ` A ) )
    <->
    B =/= 0
  ) $.

  ntp4vc-i-uint8 $e |- ( NTP4VCUint8 B ) $.
  ntp4vc-i1-uint8 $e |- ( NTP4VCUint8 A ) $.
  ntp4vc-i2-uint8 $e |- ( NTP4VCUint8 C ) $.

  ntp4vc-zero-update $e |- (
    B = 0
    ->
    C = A
  ) $.

  ntp4vc-nonzero-update $e |- (
    B =/= 0
    ->
    ( S ` ( A - ; 3 2 ) ) = C
  ) $.

  ntp4vc-toupper-post-goal0 $a |- ( T ` A ) = C $.
$}
