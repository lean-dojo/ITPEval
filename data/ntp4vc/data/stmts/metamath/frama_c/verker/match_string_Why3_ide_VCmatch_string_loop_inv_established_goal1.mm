$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/match_string_Why3_ide_VCmatch_string_loop_inv_established_goal1:
  the match-string loop-invariant establishment condition concludes that the
  real array length is nonnegative and no greater than the supplied bound,
  under the generated memory, integer-range, writable-region, valid-string,
  and valid-prefix assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCFramed,
  NTP4VCValidStr, and the signed and unsigned integer predicates directly
  expand the corresponding source definitions.

  The arbitrary total function J represents to_uint64 with its source range
  and identity laws, and K represents l_real_len with its displayed
  fixed-point and range laws. The region function and the extensions of
  linked and sconst remain arbitrary.

  The source let-bindings x = l_real_len t_2 a_1 i and
  a_2 = shift a_1 0 are expanded at every use. The quantified prefix index
  retains the full integer domain, and the existential witness in
  NTP4VCValidStr remains internal. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCMaxSint32 NTP4VCUint64Limit
  NTP4VCSint8 NTP4VCUint64
  NTP4VCValidRW NTP4VCFramed NTP4VCValidStr
  NTP4VCRealLen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-real-len-class
  $a class ( NTP4VCRealLen A B C D ) $.

ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-framed-syntax
  $a wff ( NTP4VCFramed A B ) $.
ntp4vc-valid-str-syntax
  $a wff ( NTP4VCValidStr A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-real-len-def $a |- ( NTP4VCRealLen A B C D ) =
  ( A ` <. B , <. C , D >. >. ) $.

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
) $.

ntp4vc-valid-rw-def $a |- ( ( NTP4VCValidRW A B C ) <->
  (
    0 < C
    ->
    (
      0 < ( NTP4VCBase B )
      /\
      (
        0 <_ ( NTP4VCOffset B )
        /\
        ( ( NTP4VCOffset B ) + C ) <_ ( A ` ( NTP4VCBase B ) )
      )
    )
  )
) $.

${
  $d x A B $.
  ntp4vc-framed-def $a |- ( ( NTP4VCFramed A B ) <->
    A. x e. NTP4VCAddr
      ( ( A ` ( NTP4VCBase ( B ` x ) ) ) <_ 0 )
  ) $.
$}

${
  $d x y A B C $.
  ntp4vc-valid-str-def $a |- ( ( NTP4VCValidStr A B C ) <->
    E. x e. ZZ
      (
        ( B ` ( NTP4VCShift C x ) ) = 0
        /\
        (
          ( NTP4VCUint64 x )
          /\
          (
            ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + x ) )
            /\
            A. y e. ZZ
              (
                y <_ x
                ->
                ( NTP4VCSint8 ( B ` ( NTP4VCShift C y ) ) )
              )
          )
        )
      )
  ) $.
$}

${
  $d x y z A B C D E F G H I J K $.

  $( Source parameters:
     A=t_2, B=a_1, C=i, D=a, E=t, and F=t_1.
     G is region; H and I are the linked and sconst extensions; J is
     to_uint64; and K is l_real_len. $)

  ntp4vc-pointer-memory $e |- A e.
    ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-a-address $e |- D e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-char-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- I C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-to-uint64-function $e |- J e. ( ZZ ^m ZZ ) $.

  ntp4vc-real-len-function $e |- K e.
    (
      ZZ
      ^m
      (
        ( NTP4VCAddr ^m NTP4VCAddr )
        X.
        ( NTP4VCAddr X. ZZ )
      )
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( J ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( J ` x ) = x
    ) $.

  ntp4vc-real-len-fixed-point $e |-
    A. x e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCRealLen K x y z )
            =
            if
            (
              (
                z = 0
                \/
                ( x ` ( NTP4VCShift y 0 ) ) = <. 0 , 0 >.
              ) ,
              0 ,
              (
                J
                `
                (
                  1
                  +
                  (
                    NTP4VCRealLen
                      K x
                      ( NTP4VCShift y 1 )
                      ( J ` ( z - 1 ) )
                  )
                )
              )
            )
          ) $.

  ntp4vc-real-len-range $e |-
    A. x e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          ( NTP4VCUint64 ( NTP4VCRealLen K x y z ) ) $.

  ntp4vc-region-a $e |- (
    ( G ` ( NTP4VCBase D ) ) <_ 0
  ) $.

  ntp4vc-region-a1 $e |- (
    ( G ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-i-max-sint32 $e |- C <_ NTP4VCMaxSint32 $.

  ntp4vc-pointer-memory-framed $e |- (
    NTP4VCFramed G A
  ) $.

  ntp4vc-allocation-map-linked $e |- E e. H $.

  ntp4vc-char-memory-sconst $e |- F e. I $.

  ntp4vc-i-uint64 $e |- ( NTP4VCUint64 C ) $.

  ntp4vc-a-valid-string $e |- (
    NTP4VCValidStr E F D
  ) $.

  ntp4vc-full-length-writable $e |- (
    ( NTP4VCRealLen K A B C ) = C
    ->
    (
      NTP4VCValidRW
        E
        ( NTP4VCShift B 0 )
        C
    )
  ) $.

  ntp4vc-next-byte-writable $e |- (
    ( NTP4VCRealLen K A B C ) < C
    ->
    (
      NTP4VCValidRW
        E
        ( NTP4VCShift B 0 )
        ( 1 + ( NTP4VCRealLen K A B C ) )
    )
  ) $.

  ntp4vc-real-prefix-array-strings-valid $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCRealLen K A B C )
        ->
        (
          ( NTP4VCUint64 x )
          ->
          (
            NTP4VCValidStr
              E F
              ( A ` ( NTP4VCShift B x ) )
          )
        )
      )
    ) $.

  ntp4vc-match-string-loop-inv-established-goal1 $a |- (
    ( NTP4VCRealLen K A B C ) <_ C
    /\
    0 <_ ( NTP4VCRealLen K A B C )
  ) $.
$}
