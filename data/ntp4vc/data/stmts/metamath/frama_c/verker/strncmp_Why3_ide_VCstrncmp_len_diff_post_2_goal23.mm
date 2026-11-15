$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strncmp_Why3_ide_VCstrncmp_len_diff_post_2_goal23:
  the strncmp unequal-length postcondition concludes that the comparison
  result is positive when the first bounded string is shorter than the
  second under the generated offset alignments, bounded-string validity,
  byte-comparison branch, prefix-equality, address-order, memory-linking,
  constancy, and exact integer-range assumptions. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCUint8, NTP4VCSint32, NTP4VCUint64, NTP4VCValidStr, and
  NTP4VCValidStrn directly expand the corresponding source definitions.

  The arbitrary relation N represents addr_le, with its source law under
  equal bases retained explicitly. The arbitrary map K and sets L and M
  represent region, linked, and sconst. O and P represent to_uint8 and
  to_uint64, while Q and R represent l_strlen and l_strnlen. Their exact
  range, identity, and fixed-point laws retain the relevant imported source
  theory without assigning stronger properties to these symbols.

  Every source let-binding is expanded at its uses. Both proposition-valued
  conditionals are rendered by equivalent guarded disjunctions. All
  addresses, integers, functions, relations, and predicates retain their
  unrestricted source domains. The null-position witnesses in every
  string-validity assumption remain internally existential, and all three
  prefix assumptions retain their full integer quantifiers and implication
  scopes. Splitting the source implication chain into scoped essential
  hypotheses is bidirectionally equivalent to the original statement. The
  final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint8Limit NTP4VCSint32Limit
  NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCValidRW
  NTP4VCSint8 NTP4VCUint8 NTP4VCSint32 NTP4VCUint64
  NTP4VCValidStr NTP4VCValidStrn
  NTP4VCStrlen NTP4VCStrnlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.
ntp4vc-strnlen-class $a class ( NTP4VCStrnlen A B C D ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.
ntp4vc-valid-strn-syntax $a wff ( NTP4VCValidStrn A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.
ntp4vc-strnlen-def $a |- ( NTP4VCStrnlen A B C D ) =
  ( A ` <. <. B , C >. , D >. ) $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
  <. B , C >. e. A
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

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
) $.

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
  $d x y A B C D $.
  ntp4vc-valid-strn-def $a |- ( ( NTP4VCValidStrn A B C D ) <->
    (
      ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + D ) )
      \/
      (
        E. x e. ZZ
          (
            ( B ` ( NTP4VCShift C x ) ) = 0
            /\
            (
              x < D
              /\
              (
                ( NTP4VCUint64 x )
                /\
                (
                  NTP4VCValidRW
                    A
                    ( NTP4VCShift C 0 )
                    ( 1 + x )
                )
              )
            )
          )
        /\
        A. y e. ZZ
          (
            y <_ D
            ->
            ( NTP4VCSint8 ( B ` ( NTP4VCShift C y ) ) )
          )
      )
    )
  ) $.
$}

${
  $d x y z A B C D E F G H I J K L M N O P Q R $.

  $( Source parameters:
     A=a_1, B=a_2, C=a, D=a_3, E=i_1, F=t_1, G=t, H=i_2,
     I=i_3, and J=i. K is region; L and M are the linked and sconst
     extensions; N is the addr_le extension; O and P are to_uint8 and
     to_uint64; Q and R are l_strlen and l_strnlen. Source lets are expanded
     as:
       x=offset(A), x_1=offset(B), x_2=offset(C), x_3=offset(D),
       x_4=E+offset(A)-offset(C), x_5=strnlen(F,A,E),
       x_6=offset(A)+x_5, x_7=strnlen(F,D,E), and
       x_8=E+offset(A). $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- D e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-i2-integer $e |- H e. ZZ $.
  ntp4vc-i3-integer $e |- I e. ZZ $.
  ntp4vc-i-integer $e |- J e. ZZ $.

  ntp4vc-region-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- M C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- N C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-uint8-function $e |- O e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint64-function $e |- P e. ( ZZ ^m ZZ ) $.
  ntp4vc-strlen-function $e |- Q e.
    (
      ZZ
      ^m
      ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr )
    ) $.
  ntp4vc-strnlen-function $e |- R e.
    (
      ZZ
      ^m
      ( ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) X. ZZ )
    ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe N x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-uint8-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( O ` x ) ) $.

  ntp4vc-to-uint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
      ->
      ( O ` x ) = x
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( P ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( P ` x ) = x
    ) $.

  ntp4vc-strlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        (
          ( NTP4VCStrlen Q x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( P ` ( 1 + ( NTP4VCStrlen Q x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen Q x y ) ) $.

  ntp4vc-strnlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCStrnlen R x y z )
            =
            if
            (
              (
                z = 0
                \/
                ( x ` ( NTP4VCShift y 0 ) ) = 0
              ) ,
              0 ,
              (
                P
                `
                (
                  1
                  +
                  (
                    NTP4VCStrnlen
                      R
                      x
                      ( NTP4VCShift y 1 )
                      ( P ` ( z - 1 ) )
                  )
                )
              )
            )
          ) $.

  ntp4vc-strnlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          ( NTP4VCUint64 ( NTP4VCStrnlen R x y z ) ) $.

  ntp4vc-offset-balance $e |- (
    ( ( NTP4VCOffset A ) + ( NTP4VCOffset B ) )
    =
    ( ( NTP4VCOffset C ) + ( NTP4VCOffset D ) )
  ) $.

  ntp4vc-a-length-alignment $e |- (
    (
      ( NTP4VCOffset C )
      +
      (
        NTP4VCStrnlen
          R F C
          ( ( E + ( NTP4VCOffset A ) ) - ( NTP4VCOffset C ) )
      )
    )
    =
    (
      ( NTP4VCOffset A )
      +
      ( NTP4VCStrnlen R F A E )
    )
  ) $.

  ntp4vc-a2-length-alignment $e |- (
    (
      ( NTP4VCOffset B )
      +
      (
        NTP4VCStrnlen
          R F B
          ( ( E + ( NTP4VCOffset A ) ) - ( NTP4VCOffset C ) )
      )
    )
    =
    (
      ( NTP4VCOffset D )
      +
      ( NTP4VCStrnlen R F D E )
    )
  ) $.

  ntp4vc-i1-positive $e |- 0 < E $.

  ntp4vc-a1-offset-le-a-offset $e |- (
    ( NTP4VCOffset A ) <_ ( NTP4VCOffset C )
  ) $.

  ntp4vc-region-a1 $e |- (
    ( K ` ( NTP4VCBase A ) ) <_ 0
  ) $.

  ntp4vc-region-a3 $e |- (
    ( K ` ( NTP4VCBase D ) ) <_ 0
  ) $.

  ntp4vc-first-length-shorter $e |- (
    ( NTP4VCStrnlen R F A E )
    <
    ( NTP4VCStrnlen R F D E )
  ) $.

  ntp4vc-a-offset-within-i1 $e |- (
    ( NTP4VCOffset C )
    <_
    ( E + ( NTP4VCOffset A ) )
  ) $.

  ntp4vc-linked-allocation $e |- G e. L $.
  ntp4vc-sconst-memory $e |- F e. M $.
  ntp4vc-i2-uint8 $e |- ( NTP4VCUint8 H ) $.
  ntp4vc-i3-uint8 $e |- ( NTP4VCUint8 I ) $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 J ) $.
  ntp4vc-i1-uint64 $e |- ( NTP4VCUint64 E ) $.
  ntp4vc-a1-le-a $e |- ( NTP4VCAddrLe N A C ) $.
  ntp4vc-a3-le-a2 $e |- ( NTP4VCAddrLe N D B ) $.
  ntp4vc-a1-valid-bounded-string $e |- (
    NTP4VCValidStrn G F A E
  ) $.
  ntp4vc-a3-valid-bounded-string $e |- (
    NTP4VCValidStrn G F D E
  ) $.

  ntp4vc-remaining-count-uint64 $e |- (
    NTP4VCUint64
      ( ( E + ( NTP4VCOffset A ) ) - ( NTP4VCOffset C ) )
  ) $.

  ntp4vc-a-le-a1-end $e |- (
    NTP4VCAddrLe
      N
      C
      ( NTP4VCShift A ( NTP4VCStrnlen R F A E ) )
  ) $.

  ntp4vc-a2-le-a3-end $e |- (
    NTP4VCAddrLe
      N
      B
      ( NTP4VCShift D ( NTP4VCStrnlen R F D E ) )
  ) $.

  ntp4vc-a-valid-remaining-bounded-string $e |- (
    NTP4VCValidStrn
      G F C
      ( ( E + ( NTP4VCOffset A ) ) - ( NTP4VCOffset C ) )
  ) $.

  ntp4vc-a2-valid-remaining-bounded-string $e |- (
    NTP4VCValidStrn
      G F B
      ( ( E + ( NTP4VCOffset A ) ) - ( NTP4VCOffset C ) )
  ) $.

  ntp4vc-comparison-branch $e |- (
    (
      ( E + ( NTP4VCOffset A ) ) = ( NTP4VCOffset C )
      /\
      J = 0
    )
    \/
    (
      ( E + ( NTP4VCOffset A ) ) =/= ( NTP4VCOffset C )
      /\
      (
        ( O ` ( F ` C ) ) = H
        /\
        (
          ( O ` ( F ` B ) ) = I
          /\
          (
            (
              (
                I = H
                /\
                ( J = 0 /\ I = 0 )
              )
              \/
              (
                I =/= H
                /\
                (
                  (
                    I < H
                    /\
                    J = -u 1
                  )
                  \/
                  (
                    -. ( I < H )
                    /\
                    J = 1
                  )
                )
              )
            )
            /\
            (
              (
                H = 0
                ->
                (
                  ( NTP4VCStrnlen R F A E )
                  =
                  ( NTP4VCStrlen Q F A )
                  /\
                  (
                    (
                      ( NTP4VCOffset A )
                      +
                      ( NTP4VCStrnlen R F A E )
                    )
                    =
                    ( NTP4VCOffset C )
                    /\
                    ( NTP4VCValidStr G F A )
                  )
                )
              )
              /\
              (
                I = 0
                ->
                (
                  ( NTP4VCStrnlen R F D E )
                  =
                  ( NTP4VCStrlen Q F D )
                  /\
                  (
                    (
                      ( NTP4VCOffset A )
                      +
                      ( NTP4VCStrnlen R F D E )
                    )
                    =
                    ( NTP4VCOffset C )
                    /\
                    ( NTP4VCValidStr G F D )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-prefix-equality-through-second-length $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCStrnlen R F D E )
        ->
        (
          ( F ` ( NTP4VCShift D x ) )
          =
          ( F ` ( NTP4VCShift A x ) )
        )
      )
    ) $.

  ntp4vc-prefix-equality-through-offset $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        ( x + ( NTP4VCOffset A ) ) < ( NTP4VCOffset C )
        ->
        (
          ( F ` ( NTP4VCShift D x ) )
          =
          ( F ` ( NTP4VCShift A x ) )
        )
      )
    ) $.

  ntp4vc-byte-conversion-reflects-equality $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCStrnlen R F D E )
        ->
        (
          (
            ( O ` ( F ` ( NTP4VCShift D x ) ) )
            =
            ( O ` ( F ` ( NTP4VCShift A x ) ) )
          )
          <->
          (
            ( F ` ( NTP4VCShift D x ) )
            =
            ( F ` ( NTP4VCShift A x ) )
          )
        )
      )
    ) $.

  ntp4vc-strncmp-len-diff-post-2-goal23 $a |- J = 1 $.
$}
