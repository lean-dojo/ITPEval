$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/strdup_Why3_ide_VCstrdup_call_memcpy_pre_goal4:
  the strdup verification condition concludes separation of the source and
  destination memory regions of converted string-length-plus-one size, under
  the generated nonnull, integer-range, string-length, memory-validity,
  linking, constancy, and region assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCUint32, NTP4VCSint32, and NTP4VCStringLength directly expand the
  corresponding source definitions.

  The arbitrary integer-valued map H represents region. Membership of the
  allocation map D in the arbitrary set I represents linked, while membership
  of the integer memory A in the arbitrary set J represents sconst. The
  arbitrary maps K and L respectively represent l_length specialized to A and
  to_uint32. Their relevant imported source laws are retained as explicit
  hypotheses without assigning stronger behavior to either function.

  Every source let-binding is expanded at its uses:
    x = K(B), x_1 = 1 + K(B), x_2 = L(1 + K(B)),
    and a_2 = shift(C,0).
  All address and integer parameters keep their original domains, and every
  universal condition inside the string-length predicate retains its full
  integer domain and implication scope. The final declaration is Metamath's
  native unproved $a statement encoding; this database adds no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCSint32Limit
  NTP4VCValidRW NTP4VCSeparated
  NTP4VCUint32 NTP4VCSint32 NTP4VCStringLength
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-string-length-syntax $a wff
  ( NTP4VCStringLength A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

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

ntp4vc-separated-def $a |- ( ( NTP4VCSeparated A B C D ) <->
  (
    B <_ 0
    \/
    (
      D <_ 0
      \/
      (
        ( NTP4VCBase A ) =/= ( NTP4VCBase C )
        \/
        (
          ( ( NTP4VCOffset C ) + D ) <_ ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCOffset C )
        )
      )
    )
  )
) $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

${
  $d x A B C D $.
  ntp4vc-string-length-def $a |- (
    ( NTP4VCStringLength A B C D )
    <->
    (
      ( B ` ( NTP4VCShift C D ) ) = 0
      /\
      (
        0 <_ D
        /\
        (
          ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + D ) )
          /\
          A. x e. ZZ
            (
              0 <_ x
              ->
              (
                x < D
                ->
                ( B ` ( NTP4VCShift C x ) ) =/= 0
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d x y A B C D E F G H I J K L $.

  $( Source parameters:
     A=t_1, B=a, C=a_1, D=t, E=i, F=i_1, and G=i_2.
     H is region; I and J are the linked and sconst extensions; K is
     l_length specialized to A; and L is to_uint32. Source lets are expanded
     as x=K(B), x_1=1+K(B), x_2=L(1+K(B)), and a_2=shift(C,0). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- D e. ( ZZ ^m ZZ ) $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-i2-integer $e |- G e. ZZ $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- J C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-length-map $e |- K e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-to-uint32-function $e |- L e. ( ZZ ^m ZZ ) $.

  ntp4vc-length-law $e |- A. x e. NTP4VCAddr A. y e. ZZ
    (
      ( NTP4VCStringLength D A x y )
      ->
      ( K ` x ) = y
    ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( L ` x ) ) $.

  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( L ` x ) = x
    ) $.

  ntp4vc-a1-nonnull $e |- C =/= <. 0 , 0 >. $.

  ntp4vc-converted-size-nonzero $e |- (
    ( L ` ( 1 + ( K ` B ) ) ) =/= 0
  ) $.

  ntp4vc-region-a $e |- (
    ( H ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- D e. I $.
  ntp4vc-sconst-memory $e |- A e. J $.

  ntp4vc-length-sint32 $e |- (
    NTP4VCSint32 ( K ` B )
  ) $.

  ntp4vc-string-length-i $e |- (
    NTP4VCStringLength D A B E
  ) $.

  ntp4vc-string-length-i1 $e |- (
    NTP4VCStringLength D A B F
  ) $.

  ntp4vc-string-length-i2 $e |- (
    NTP4VCStringLength D A B G
  ) $.

  ntp4vc-size-sint32 $e |- (
    NTP4VCSint32 ( 1 + ( K ` B ) )
  ) $.

  ntp4vc-destination-valid-if-positive $e |- (
    0 < ( L ` ( 1 + ( K ` B ) ) )
    ->
    (
      NTP4VCValidRW
        D
        ( NTP4VCShift C 0 )
        ( L ` ( 1 + ( K ` B ) ) )
    )
  ) $.

  ntp4vc-strdup-call-memcpy-pre-goal4 $a |- (
    NTP4VCSeparated
      ( NTP4VCShift B 0 )
      ( L ` ( 1 + ( K ` B ) ) )
      ( NTP4VCShift C 0 )
      ( L ` ( 1 + ( K ` B ) ) )
  ) $.
$}
