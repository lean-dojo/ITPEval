$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_binvert_limbqtvc: the verification condition
  for Newton-style inversion of an odd unsigned 64-bit limb, including the
  eight-bit lookup-table seed and three precision-doubling updates. This file
  contains no proof.

  Source 64-bit words are represented exactly by the integer interval
  [0, 2^64 - 1], in bijection with unsigned limb values. All divisors in the
  quotient, modulo, and power-of-two congruences are positive under their
  enclosing assumptions, so Metamath's floor quotient and modulo agree with
  Why3's Euclidean operations. The predicates below are definitional
  abbreviations for the source's nested universal quantifiers and implications.
$)

$[ lib/set.mm $]

$c NTP4VCWord64 NTP4VCUInt64InBounds NTP4VCOdd
   NTP4VCDoublePrecision NTP4VCAfterO13 NTP4VCAfterO12
   NTP4VCAfterO11 NTP4VCAfterO10 NTP4VCAfterO9 NTP4VCAfterO8
   NTP4VCAfterO7 NTP4VCAfterO6 NTP4VCAfterO5 NTP4VCAfterO4
   NTP4VCAfterO3 NTP4VCAfterO2 NTP4VCTableStage NTP4VCHStage
   NTP4VCO1Stage $.

ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-uint64-in-bounds-syntax $a wff NTP4VCUInt64InBounds A $.
ntp4vc-odd-syntax $a wff NTP4VCOdd A $.
ntp4vc-double-precision-syntax $a wff NTP4VCDoublePrecision $.
ntp4vc-after-o13-syntax $a wff NTP4VCAfterO13 A B C $.
ntp4vc-after-o12-syntax $a wff NTP4VCAfterO12 A B C $.
ntp4vc-after-o11-syntax $a wff NTP4VCAfterO11 A B C $.
ntp4vc-after-o10-syntax $a wff NTP4VCAfterO10 A B $.
ntp4vc-after-o9-syntax $a wff NTP4VCAfterO9 A B C $.
ntp4vc-after-o8-syntax $a wff NTP4VCAfterO8 A B C $.
ntp4vc-after-o7-syntax $a wff NTP4VCAfterO7 A B C $.
ntp4vc-after-o6-syntax $a wff NTP4VCAfterO6 A B $.
ntp4vc-after-o5-syntax $a wff NTP4VCAfterO5 A B C $.
ntp4vc-after-o4-syntax $a wff NTP4VCAfterO4 A B C $.
ntp4vc-after-o3-syntax $a wff NTP4VCAfterO3 A B C $.
ntp4vc-after-o2-syntax $a wff NTP4VCAfterO2 A B $.
ntp4vc-table-stage-syntax $a wff NTP4VCTableStage A B $.
ntp4vc-h-stage-syntax $a wff NTP4VCHStage A B $.
ntp4vc-o1-stage-syntax $a wff NTP4VCO1Stage A $.

ntp4vc-word64-definition $a
  |- NTP4VCWord64 = ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-uint64-in-bounds-definition $a
  |- NTP4VCUInt64InBounds A <-> A e. NTP4VCWord64 $.

${
  $d q A $.
  ntp4vc-odd-definition $a
    |- NTP4VCOdd A <->
       E. q e. ZZ ( A = ( ( 2 x. q ) + 1 ) ) $.
$}

${
  $d q r $.
  $d q s $.
  $d r s $.
  ntp4vc-double-precision-definition $a
    |- NTP4VCDoublePrecision <->
       A. q e. ZZ A. r e. ZZ A. s e. ZZ
       (
         (
           (
             ( ( 0 <_ q ) /\ ( 0 <_ r ) )
             /\
             (
               ( ( ( r x. q ) mod ( 2 ^ s ) ) = 1 )
               /\
               ( ( 0 <_ ( 2 x. s ) ) /\ ( ( 2 x. s ) <_ ; 6 4 ) )
             )
           )
           ->
           (
             (
               (
                 (
                   ( ( 2 x. r ) - ( r x. ( r x. q ) ) )
                   mod ( 2 ^ ; 6 4 )
                 )
                 x. q
               )
               mod ( 2 ^ ( 2 x. s ) )
             )
             = 1
           )
         )
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o13-definition $a
    |- NTP4VCAfterO13 A B C <->
       A. q e. NTP4VCWord64
       (
         (
           q = ( ( C - B ) mod ( 2 ^ ; 6 4 ) )
         )
         ->
         ( ( ( q x. A ) mod ( 2 ^ ; 6 4 ) ) = 1 )
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o12-definition $a
    |- NTP4VCAfterO12 A B C <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( 2 x. B ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO13 A C q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o11-definition $a
    |- NTP4VCAfterO11 A B C <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( B x. C ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO12 A B q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  ntp4vc-after-o10-definition $a
    |- NTP4VCAfterO10 A B <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( B x. A ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO11 A B q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o9-definition $a
    |- NTP4VCAfterO9 A B C <->
       A. q e. NTP4VCWord64
       (
         (
           q = ( ( C - B ) mod ( 2 ^ ; 6 4 ) )
         )
         ->
         NTP4VCAfterO10 A q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o8-definition $a
    |- NTP4VCAfterO8 A B C <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( 2 x. B ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO9 A C q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o7-definition $a
    |- NTP4VCAfterO7 A B C <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( B x. C ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO8 A B q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  ntp4vc-after-o6-definition $a
    |- NTP4VCAfterO6 A B <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( B x. A ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO7 A B q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o5-definition $a
    |- NTP4VCAfterO5 A B C <->
       A. q e. NTP4VCWord64
       (
         (
           q = ( ( C - B ) mod ( 2 ^ ; 6 4 ) )
         )
         ->
         NTP4VCAfterO6 A q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o4-definition $a
    |- NTP4VCAfterO4 A B C <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( 2 x. B ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO5 A C q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  $d q C $.
  ntp4vc-after-o3-definition $a
    |- NTP4VCAfterO3 A B C <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( B x. C ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO4 A B q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  ntp4vc-after-o2-definition $a
    |- NTP4VCAfterO2 A B <->
       A. q e. NTP4VCWord64
       (
         ( q = ( ( B x. A ) mod ( 2 ^ ; 6 4 ) ) )
         ->
         NTP4VCAfterO3 A B q
       ) $.
$}

${
  $d q A $.
  $d q B $.
  ntp4vc-table-stage-definition $a
    |- NTP4VCTableStage A B <->
       A. q e. NTP4VCWord64
       (
         (
           (
             ( ( 0 <_ q ) /\ ( q < ; ; 2 5 6 ) )
             /\
             (
               (
                 ( q x. ( ( 2 x. B ) + 1 ) )
                 mod ( 2 ^ 8 )
               )
               = 1
             )
           )
           ->
           NTP4VCAfterO2 A q
         )
       ) $.
$}

${
  $d q A $.
  $d q B $.
  ntp4vc-h-stage-definition $a
    |- NTP4VCHStage A B <->
       A. q e. NTP4VCWord64
       (
         ( q = ( B mod ; ; 1 2 8 ) )
         ->
         (
           ( ( 0 <_ q ) /\ ( q < ; ; 1 2 8 ) )
           /\
           NTP4VCTableStage A q
         )
       ) $.
$}

${
  $d q A $.
  ntp4vc-o1-stage-definition $a
    |- NTP4VCO1Stage A <->
       A. q e. NTP4VCWord64
       (
         ( q = ( |_ ` ( A / 2 ) ) )
         ->
         (
           (
             ( -. ( ; ; 1 2 8 = 0 ) )
             /\
             NTP4VCUInt64InBounds ( q mod ; ; 1 2 8 )
           )
           /\
           NTP4VCHStage A q
         )
       ) $.
$}

${
  ntp4vc-n-word64 $e |- A e. NTP4VCWord64 $.
  ntp4vc-fact0 $e |- NTP4VCOdd A $.

  powm-Powm-binvert-limb-vc $a
    |- (
         NTP4VCDoublePrecision
         /\
         (
           ( -. ( 2 = 0 ) )
           /\
           (
             NTP4VCUInt64InBounds ( |_ ` ( A / 2 ) )
             /\
             NTP4VCO1Stage A
           )
         )
       ) $.
$}
