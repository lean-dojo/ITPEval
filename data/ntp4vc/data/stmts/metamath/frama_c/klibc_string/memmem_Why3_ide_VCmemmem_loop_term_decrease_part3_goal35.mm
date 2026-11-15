$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/memmem_Why3_ide_VCmemmem_loop_term_decrease_part3_goal35:
  the memmem loop-termination verification condition states that the current
  unsigned search offset is strictly below its converted successor, under
  the generated integer-range, byte-memory, allocation-validity, separation,
  linking, and quantified mismatch assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCUint32, and NTP4VCUint8 directly expand the corresponding source
  definitions.

  The arbitrary integer-valued map R represents the source region function,
  and membership of the allocation map K in the arbitrary set L represents
  linked. The arbitrary integer function U represents to_uint32. Its source
  laws that every result is uint32 and that every uint32 input is fixed are
  retained explicitly; together they also imply its source idempotence law,
  without imposing a stronger wraparound definition.

  All source let-bindings are expanded at their uses. The existential and
  universal mismatch conditions retain their full integer domains and their
  original implication scopes. The final declaration is Metamath's native
  unproved $a statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRW NTP4VCSeparated NTP4VCUint32 NTP4VCUint8
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
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

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

${
  $d x y A B C D E F G H I J K L M N P Q R U $.

  $( Source parameters:
     A=a_8, B=a_9, C=t_1, D=a_1, E=a, F=i_2, G=a_6, H=i_1,
     I=a_7, J=i, K=t, M=a_5, N=a_4, P=a_3, and Q=a_2.
     R is region, L is the extension of linked, and U is to_uint32.

     Source lets are expanded as:
       x=base(A), x_1=base(B), x_2=C(shift(D,0)),
       x_3=C(shift(E,F)), x_4=C(shift(D,1)),
       x_5=U(1+F), x_6=C(shift(E,U(1+F))),
       a_10=shift(A,0), a_11=shift(B,0), a_12=shift(G,0),
       x_7=U(H-2), and a_13=shift(I,0). $)

  ntp4vc-a8-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a9-address $e |- B e. NTP4VCAddr $.
  ntp4vc-value-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- D e. NTP4VCAddr $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- F e. ZZ $.
  ntp4vc-a6-address $e |- G e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- H e. ZZ $.
  ntp4vc-a7-address $e |- I e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- J e. ZZ $.
  ntp4vc-allocation-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-a5-address $e |- M e. NTP4VCAddr $.
  ntp4vc-a4-address $e |- N e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- P e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- Q e. NTP4VCAddr $.

  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- U e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( U ` x ) ) $.

  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( U ` x ) = x
    ) $.

  ntp4vc-i-nonzero $e |- J =/= 0 $.
  ntp4vc-i1-nonzero $e |- H =/= 0 $.
  ntp4vc-i1-not-one $e |- H =/= 1 $.

  ntp4vc-a8-base $e |- (
    ( NTP4VCBase A ) = ( NTP4VCBase D )
  ) $.

  ntp4vc-a9-base $e |- (
    ( NTP4VCBase B ) = ( NTP4VCBase E )
  ) $.

  ntp4vc-current-byte-differs $e |- (
    ( C ` ( NTP4VCShift D 0 ) )
    =/=
    ( C ` ( NTP4VCShift E F ) )
  ) $.

  ntp4vc-adjacent-byte-equals-start $e |- (
    ( C ` ( NTP4VCShift D 1 ) )
    =
    ( C ` ( NTP4VCShift D 0 ) )
  ) $.

  ntp4vc-successor-byte-equals-adjacent $e |- (
    ( C ` ( NTP4VCShift E ( U ` ( 1 + F ) ) ) )
    =
    ( C ` ( NTP4VCShift D 1 ) )
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ J $.
  ntp4vc-i1-le-i $e |- H <_ J $.
  ntp4vc-i1-nonnegative $e |- 0 <_ H $.
  ntp4vc-i2-nonnegative $e |- 0 <_ F $.

  ntp4vc-region-a8 $e |- (
    ( R ` ( NTP4VCBase A ) ) <_ 0
  ) $.

  ntp4vc-region-a9 $e |- (
    ( R ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-i2-bounded-by-remainder $e |- (
    F <_ ( U ` ( J - H ) )
  ) $.

  ntp4vc-index-sum-bound $e |- (
    ( H + F ) <_ ( 2 + J )
  ) $.

  ntp4vc-linked-allocation $e |- K e. L $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 J ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 H ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 F ) $.

  ntp4vc-current-byte-uint8 $e |- (
    NTP4VCUint8 ( C ` ( NTP4VCShift E F ) )
  ) $.

  ntp4vc-start-byte-uint8 $e |- (
    NTP4VCUint8 ( C ` ( NTP4VCShift D 0 ) )
  ) $.

  ntp4vc-adjacent-byte-uint8 $e |- (
    NTP4VCUint8 ( C ` ( NTP4VCShift D 1 ) )
  ) $.

  ntp4vc-a8-valid-rw $e |- (
    NTP4VCValidRW K ( NTP4VCShift A 0 ) H
  ) $.

  ntp4vc-a9-valid-rw $e |- (
    NTP4VCValidRW K ( NTP4VCShift B 0 ) J
  ) $.

  ntp4vc-a9-a8-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCShift B 0 ) J
      ( NTP4VCShift A 0 ) H
  ) $.

  ntp4vc-a6-valid-rw $e |- (
    NTP4VCValidRW
      K
      ( NTP4VCShift G 0 )
      ( U ` ( H - 2 ) )
  ) $.

  ntp4vc-a7-valid-rw $e |- (
    NTP4VCValidRW
      K
      ( NTP4VCShift I 0 )
      ( U ` ( H - 2 ) )
  ) $.

  ntp4vc-a7-a6-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCShift I 0 )
      ( U ` ( H - 2 ) )
      ( NTP4VCShift G 0 )
      ( U ` ( H - 2 ) )
  ) $.

  ntp4vc-successor-byte-uint8 $e |- (
    NTP4VCUint8
      ( C ` ( NTP4VCShift E ( U ` ( 1 + F ) ) ) )
  ) $.

  ntp4vc-no-tail-difference $e |- (
    0 < ( U ` ( H - 2 ) )
    ->
    -. E. x e. ZZ
      (
        (
          ( C ` ( NTP4VCShift M x ) )
          =/=
          ( C ` ( NTP4VCShift N x ) )
        )
        /\
        (
          0 <_ x
          /\
          x < ( U ` ( H - 2 ) )
        )
      )
  ) $.

  ntp4vc-prior-mismatch-witnesses $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < F
        ->
        E. y e. ZZ
          (
            0 <_ y
            ->
            (
              ( 3 + y ) <_ H
              ->
              (
                (
                  C
                  `
                  ( NTP4VCShift P ( ( 2 + y ) + x ) )
                )
                =/=
                (
                  C
                  `
                  ( NTP4VCShift Q ( 2 + y ) )
                )
              )
            )
          )
      )
    ) $.

  ntp4vc-memmem-loop-term-decrease-part3-goal35 $a |- (
    F < ( U ` ( 1 + F ) )
  ) $.
$}
