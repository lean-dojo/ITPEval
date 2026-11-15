$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/add_Add_add_n_rxyqtvc: the verification condition for
  doubling an in-place multiprecision integer, including 32- and 64-bit word
  semantics, carry arithmetic, total integer-indexed memory framing, and
  preservation of pointer bounds and length metadata. This file contains no
  proof.

  Pointer data retains the source array's total ZZ-indexed limb map and
  independent nonnegative-integer length, together with integer offset and
  bounds, a writability bit, and an arbitrary nonempty zone. The predicates
  below are definitional abbreviations for source validity, multiprecision
  value, metadata equality, framing, and the complete verification condition.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCPlength
  NTP4VCOffset NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone
  NTP4VCToNat NTP4VCPelts NTP4VCValid NTP4VCValue
  NTP4VCSameMeta NTP4VCFrame NTP4VCCorePost NTP4VCVC
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syn $a wff NTP4VCInt32InBounds A $.
ntp4vc-ptr-syn $a class ( NTP4VCPtr A ) $.
ntp4vc-data-syn $a class ( NTP4VCData A ) $.
ntp4vc-length-syn $a class ( NTP4VCLength A ) $.
ntp4vc-plength-syn $a class ( NTP4VCPlength A ) $.
ntp4vc-offset-syn $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syn $a class ( NTP4VCMin A ) $.
ntp4vc-max-syn $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syn $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syn $a class ( NTP4VCZone A ) $.
ntp4vc-to-nat-syn $a class ( NTP4VCToNat A ) $.
ntp4vc-pelts-syn $a class ( NTP4VCPelts A B ) $.
ntp4vc-valid-syn $a wff NTP4VCValid A B $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-same-meta-syn $a wff NTP4VCSameMeta A B $.
ntp4vc-frame-syn $a wff NTP4VCFrame A B C $.
ntp4vc-core-post-syn $a wff NTP4VCCorePost A B C D $.
ntp4vc-vc-syn $a wff NTP4VCVC A B C $.

ntp4vc-word32-def $a
  |- NTP4VCWord32 = ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) )
$.

ntp4vc-word64-def $a
  |- NTP4VCWord64 = ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) )
$.

ntp4vc-signed32-def $a
  |- ( NTP4VCSigned32 A ) =
      if ( A < ( 2 ^ ; 3 1 ) , A , ( A - ( 2 ^ ; 3 2 ) ) )
$.

ntp4vc-int32-in-bounds-def $a
  |- ( NTP4VCInt32InBounds A <->
      ( A e. ZZ /\
        ( ( -u ( 2 ^ ; 3 1 ) ) <_ A /\ A < ( 2 ^ ; 3 1 ) ) ) )
$.

ntp4vc-ptr-def $a
  |- ( NTP4VCPtr A ) =
      ( ( ( NTP4VCWord64 ^m ZZ ) X. NN0 ) X.
        ( ZZ X. ( ZZ X. ( ZZ X. ( 2 X. A ) ) ) ) )
$.

ntp4vc-data-def $a
  |- ( NTP4VCData A ) = ( 1st ` A )
$.

ntp4vc-length-def $a
  |- ( NTP4VCLength A ) = ( 2nd ` ( NTP4VCData A ) )
$.

ntp4vc-plength-def $a
  |- ( NTP4VCPlength A ) = ( NTP4VCLength A )
$.

ntp4vc-offset-def $a
  |- ( NTP4VCOffset A ) = ( 1st ` ( 2nd ` A ) )
$.

ntp4vc-min-def $a
  |- ( NTP4VCMin A ) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
$.

ntp4vc-max-def $a
  |- ( NTP4VCMax A ) =
      ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) )
$.

ntp4vc-writable-def $a
  |- ( NTP4VCWritable A ) =
      ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) )
$.

ntp4vc-zone-def $a
  |- ( NTP4VCZone A ) =
      ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) )
$.

ntp4vc-to-nat-def $a
  |- ( NTP4VCToNat A ) = if ( 0 <_ A , A , 0 )
$.

ntp4vc-pelts-def $a
  |- ( NTP4VCPelts A B ) =
      ( ( 1st ` ( NTP4VCData A ) ) ` B )
$.

ntp4vc-valid-def $a
  |- ( NTP4VCValid A B <->
      ( NTP4VCInt32InBounds B /\
        ( 0 <_ B /\
          ( ( 0 <_ ( NTP4VCMin A ) /\
              ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) ) /\
            ( ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) /\
              ( NTP4VCMax A ) <_ ( NTP4VCPlength A ) ) ) ) ) )
$.

${
  $d k A B $.
  ntp4vc-value-def $a
    |- ( NTP4VCValue A B ) =
        sum_ k e. ( 0 ..^ ( NTP4VCToNat B ) )
          ( ( NTP4VCPelts A ( ( NTP4VCOffset A ) + k ) ) x.
            ( ( 2 ^ ; 6 4 ) ^ k ) )
  $.
$}

ntp4vc-same-meta-def $a
  |- ( NTP4VCSameMeta A B <->
      ( ( NTP4VCLength A ) = ( NTP4VCLength B ) /\
        ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
          ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
            ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
              ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
                ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) ) ) )
$.

${
  $d j A B C $.
  ntp4vc-frame-def $a
    |- ( NTP4VCFrame A B C <->
        A. j e. ZZ
          ( ( j < ( NTP4VCOffset A ) \/
              ( ( NTP4VCOffset A ) + C ) <_ j ) ->
            ( NTP4VCPelts A j ) = ( NTP4VCPelts B j ) ) )
  $.
$}

ntp4vc-core-post-def $a
  |- ( NTP4VCCorePost A B C D <->
      ( ( ( NTP4VCValue A C ) +
          ( ( ( 2 ^ ; 6 4 ) ^ ( NTP4VCToNat C ) ) x. D ) ) =
          ( ( NTP4VCValue B C ) + ( NTP4VCValue B C ) ) /\
        ( ( 0 <_ D /\ D <_ 1 ) /\ NTP4VCFrame A B C ) ) )
$.

${
  $d x r A B C $.
  ntp4vc-vc-def $a
    |- ( NTP4VCVC A B C <->
        ( 0 <_ ( NTP4VCSigned32 B ) /\
          ( NTP4VCValid A ( NTP4VCSigned32 B ) /\
            ( ( NTP4VCWritable A ) = 1 /\
              A. x e. ( NTP4VCPtr C )
                ( NTP4VCSameMeta x A ->
                  A. r e. NTP4VCWord64
                    ( NTP4VCCorePost
                        x A ( NTP4VCSigned32 B ) r ->
                      ( NTP4VCCorePost
                          x A ( NTP4VCSigned32 B ) r /\
                        ( ( NTP4VCMin x ) = ( NTP4VCMin A ) /\
                          ( ( NTP4VCMax x ) = ( NTP4VCMax A ) /\
                            ( NTP4VCPlength x ) =
                            ( NTP4VCPlength A ) ) ) ) ) ) ) ) ) )
  $.
$}

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-size-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-pointer-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-size-nonnegative $e |- 0 <_ ( NTP4VCSigned32 B ) $.
  ntp4vc-pointer-writable $e |- ( NTP4VCWritable A ) = 1 $.
  ntp4vc-pointer-valid $e
    |- NTP4VCValid A ( NTP4VCSigned32 B )
  $.

  ntp4vc-add-n-rxy-statement $a
    |- NTP4VCVC A B Z
  $.
$}
