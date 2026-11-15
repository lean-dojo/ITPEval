$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_a2_established_goal16:
  the should-we-balance loop invariant states that the selected CPU remains
  in the original balance mask after a havoc update, under the source integer
  bounds, memory validity, framing, linking, separation, mask-equivalence,
  and quantified scheduler-mask assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented by ZZ X. ZZ. The named operations and source
  let-bound values below are explicit conservative definitions of base,
  offset, shift, havoc, storage lookup, validity, separation, framing, C
  integer ranges, and a_2 through a_18.

  The arbitrary maps I through O represent region, the extension of linked,
  l_size, l_sched_group_cpus, l_sched_group_mask, l_group_balance_mask, and
  l_cpu_smt_mask as described at the parameter block. Splitting the source
  curried implication chain into scoped essential hypotheses is
  bidirectionally equivalent to the original statement. Quantifiers retain
  the full source integer and address domains. The final declaration is
  Metamath's native unproved $a statement encoding; there is no $p proof.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCHavoc
  NTP4VCStorage NTP4VCMaxSint32 NTP4VCSint32Limit
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCUint8
  NTP4VCA2 NTP4VCX NTP4VCA3 NTP4VCA4 NTP4VCA5 NTP4VCA6
  NTP4VCX1 NTP4VCX2 NTP4VCA7 NTP4VCA8 NTP4VCA9 NTP4VCA10
  NTP4VCA11 NTP4VCA12 NTP4VCA13 NTP4VCA14 NTP4VCA15
  NTP4VCA16 NTP4VCA17 NTP4VCA18
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-storage-class $a class ( NTP4VCStorage A B ) $.

ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax $a wff ( NTP4VCFramed A B ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.

ntp4vc-a2-class $a class ( NTP4VCA2 A ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B C ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B C ) $.
ntp4vc-a9-class $a class ( NTP4VCA9 A B C ) $.
ntp4vc-a10-class $a class ( NTP4VCA10 A B C D E F ) $.
ntp4vc-a11-class $a class ( NTP4VCA11 A ) $.
ntp4vc-a12-class $a class ( NTP4VCA12 A B ) $.
ntp4vc-a13-class $a class ( NTP4VCA13 A B ) $.
ntp4vc-a14-class $a class ( NTP4VCA14 A B ) $.
ntp4vc-a15-class $a class ( NTP4VCA15 A B C ) $.
ntp4vc-a16-class $a class ( NTP4VCA16 A B C ) $.
ntp4vc-a17-class $a class ( NTP4VCA17 A B ) $.
ntp4vc-a18-class $a class ( NTP4VCA18 A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

${
  $d x A B C D $.
  ntp4vc-havoc-def $a |- ( NTP4VCHavoc A B C D ) =
    (
      x e. NTP4VCAddr |->
        if
        (
          ( NTP4VCSeparated x 1 C D ) ,
          ( B ` x ) ,
          ( A ` x )
        )
    ) $.
$}

ntp4vc-storage-def $a |- ( NTP4VCStorage A B ) =
  ( NTP4VCShift ( A ` ( NTP4VCShift B 0 ) ) 0 ) $.

ntp4vc-valid-rd-def $a |- ( ( NTP4VCValidRD A B C ) <->
  (
    0 < C
    ->
    (
      ( NTP4VCBase B ) =/= 0
      /\
      (
        0 <_ ( NTP4VCOffset B )
        /\
        ( ( NTP4VCOffset B ) + C ) <_ ( A ` ( NTP4VCBase B ) )
      )
    )
  )
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

${
  $d x A B $.
  ntp4vc-framed-def $a |- ( ( NTP4VCFramed A B ) <->
    A. x e. NTP4VCAddr
      ( ( A ` ( NTP4VCBase ( B ` x ) ) ) <_ 0 )
  ) $.
$}

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

ntp4vc-a2-def $a |- ( NTP4VCA2 A ) = ( NTP4VCShift A 3 ) $.
ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A ` ( NTP4VCA2 B ) ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A ) = ( NTP4VCShift A 4 ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B ) = ( A ` ( NTP4VCA3 B ) ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B ) =
  ( A ` ( NTP4VCShift ( NTP4VCA4 A B ) 0 ) ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A ) = ( NTP4VCShift A 1 ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A B ) = ( A ` ( NTP4VCA6 B ) ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B C ) =
  (
    A
    `
    ( NTP4VCShift ( NTP4VCA5 B C ) ( NTP4VCX1 A C ) )
  ) $.

ntp4vc-a7-def $a |- ( NTP4VCA7 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a8-def $a |- ( NTP4VCA8 A B C ) =
  ( A ` ( NTP4VCShift ( NTP4VCA7 B C ) 0 ) ) $.
ntp4vc-a9-def $a |- ( NTP4VCA9 A B C ) =
  ( NTP4VCShift ( NTP4VCA8 A B C ) 0 ) $.
ntp4vc-a10-def $a |- ( NTP4VCA10 A B C D E F ) =
  ( NTP4VCHavoc A B ( NTP4VCA9 C D E ) F ) $.
ntp4vc-a11-def $a |- ( NTP4VCA11 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a12-def $a |- ( NTP4VCA12 A B ) =
  ( A ` ( NTP4VCA11 B ) ) $.
ntp4vc-a13-def $a |- ( NTP4VCA13 A B ) =
  ( NTP4VCShift ( NTP4VCA12 A B ) 0 ) $.
ntp4vc-a14-def $a |- ( NTP4VCA14 A B ) =
  ( A ` ( NTP4VCA13 A B ) ) $.
ntp4vc-a15-def $a |- ( NTP4VCA15 A B C ) =
  ( A ` ( NTP4VCA14 B C ) ) $.
ntp4vc-a16-def $a |- ( NTP4VCA16 A B C ) =
  ( A ` ( NTP4VCShift ( NTP4VCA15 B A C ) 0 ) ) $.
ntp4vc-a17-def $a |- ( NTP4VCA17 A B ) =
  ( NTP4VCShift ( NTP4VCA5 A B ) 0 ) $.
ntp4vc-a18-def $a |- ( NTP4VCA18 A B C ) =
  ( NTP4VCShift ( NTP4VCA16 A B C ) 0 ) $.

${
  $d x y z w v A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=a_1, B=t_2, C=t_3, D=a, E=i, F=t_1, G=i_1, H=t.
     I is region, J is the extension of linked, K is l_size,
     L is l_sched_group_cpus, M is l_sched_group_mask,
     N is l_group_balance_mask, and O is l_cpu_smt_mask. $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-t2-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t3-pointer-map $e |- C e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- D e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-t1-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- K e. ZZ $.
  ntp4vc-sched-group-cpus-function
    $e |- L e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-sched-group-mask-function
    $e |- M e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-group-balance-mask-function
    $e |- N e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-cpu-smt-mask-function
    $e |- O e. ( NTP4VCAddr ^m ZZ ) $.
  ntp4vc-idle-cpu-function $e |- P e. ( ZZ ^m ZZ ) $.

  itpeval-q-tl-idle-cpu $e |- A. x e. ZZ
    (
      0 <_ ( P ` x )
      /\
      ( P ` x ) < ; ; 2 5 6
    ) $.

  itpeval-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NTP4VCAddr )
      A. z e. ( NTP4VCAddr ^m NTP4VCAddr )
        (
          0 <_ x
          ->
          (
            x < K
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( O ` x ) 0 ) ) x )
            ) =/= 0
          )
        ) $.

  itpeval-q-mask-symm $e |- A. z e. ( ZZ ^m NTP4VCAddr )
    A. w e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. ZZ
        A. x e. ZZ
          (
            (
              z `
              ( NTP4VCShift ( w ` ( NTP4VCShift ( O ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < K
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < K
                    ->
                    (
                      z `
                      ( NTP4VCShift
                        ( w ` ( NTP4VCShift ( O ` x ) 0 ) ) y )
                    ) =/= 0
                  )
                )
              )
            )
          ) $.

  itpeval-q-mask-trans $e |- A. w e. ( NTP4VCAddr ^m NTP4VCAddr )
    A. x e. ZZ
      A. z e. ( ZZ ^m NTP4VCAddr )
        A. y e. ZZ
          A. v e. ZZ
            (
              (
                z `
                ( NTP4VCShift
                  ( w ` ( NTP4VCShift ( O ` x ) 0 ) ) y )
              ) =/= 0
              ->
              (
                (
                  z `
                  ( NTP4VCShift
                    ( w ` ( NTP4VCShift ( O ` y ) 0 ) ) v )
                ) =/= 0
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < K
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < K
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < K
                            ->
                            (
                              z `
                              ( NTP4VCShift
                                ( w ` ( NTP4VCShift ( O ` x ) 0 ) ) v )
                            ) =/= 0
                          )
                        )
                      )
                    )
                  )
                )
              )
            ) $.


  ntp4vc-size-properties $e |- (
    0 < K
    /\
    K <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-x-not-two $e |- ( NTP4VCX B A ) =/= 2 $.
  ntp4vc-x2-nonzero $e |- ( NTP4VCX2 B C A ) =/= 0 $.
  ntp4vc-selected-a16-nonzero $e |- (
    (
      ( NTP4VCA10 F B C D E K )
      `
      ( NTP4VCShift ( NTP4VCA16 C N A ) G )
    )
    =/=
    0
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ E $.
  ntp4vc-i-lt-size $e |- E < K $.
  ntp4vc-i1-nonnegative $e |- 0 <_ G $.
  ntp4vc-i1-lt-size $e |- G < K $.
  ntp4vc-x1-nonnegative $e |- 0 <_ ( NTP4VCX1 B A ) $.
  ntp4vc-x1-lt-size $e |- ( NTP4VCX1 B A ) < K $.

  ntp4vc-region-a $e |- ( I ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( I ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed I C ) $.
  ntp4vc-linked-allocation $e |- H e. J $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-a1-valid-rd $e |- ( NTP4VCValidRD H A 5 ) $.
  ntp4vc-x-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX B A ) ) $.
  ntp4vc-x1-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX1 B A ) ) $.
  ntp4vc-a3-valid-rd $e |- ( NTP4VCValidRD H ( NTP4VCA3 A ) 1 ) $.
  ntp4vc-a6-valid-rd $e |- ( NTP4VCValidRD H ( NTP4VCA6 A ) 1 ) $.
  ntp4vc-a2-valid-rd $e |- ( NTP4VCValidRD H ( NTP4VCA2 A ) 1 ) $.
  ntp4vc-a11-valid-rd $e |- ( NTP4VCValidRD H ( NTP4VCA11 A ) 1 ) $.
  ntp4vc-a7-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA7 D E ) 1
  ) $.
  ntp4vc-a4-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA4 C A ) 1
  ) $.
  ntp4vc-a1-field-valid-rd $e |- (
    NTP4VCValidRD H ( C ` ( NTP4VCShift A 2 ) ) 2
  ) $.
  ntp4vc-a12-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA12 C A ) 2
  ) $.
  ntp4vc-a12-field-sint32 $e |- (
    NTP4VCSint32
      ( B ` ( NTP4VCShift ( NTP4VCA12 C A ) 1 ) )
  ) $.
  ntp4vc-a13-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA13 C A ) 1
  ) $.
  ntp4vc-a14-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA14 C A ) 1
  ) $.
  ntp4vc-a15-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA15 N C A ) 1
  ) $.
  ntp4vc-x2-uint8 $e |- ( NTP4VCUint8 ( NTP4VCX2 B C A ) ) $.
  ntp4vc-a17-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA17 C A ) K
  ) $.
  ntp4vc-a9-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA9 C D E ) K
  ) $.
  ntp4vc-a18-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA18 C N A ) K
  ) $.
  ntp4vc-a9-a18-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCA9 C D E ) K
      ( NTP4VCA18 C N A ) K
  ) $.

  ntp4vc-a17-separated-from-cpu-storage $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < K
        ->
        (
          NTP4VCSeparated
            ( NTP4VCA17 C A ) K
            ( NTP4VCStorage C ( NTP4VCShift D x ) ) K
        )
      )
    ) $.

  ntp4vc-cpu-storage-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < K
        ->
        (
          NTP4VCValidRD H ( NTP4VCShift D x ) 1
          /\
          (
            NTP4VCValidRW
              H
              ( NTP4VCStorage C ( NTP4VCShift D x ) )
              K
          )
        )
      )
    ) $.

  ntp4vc-havoc-mask-equivalence $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < K
        ->
        (
          (
            ( NTP4VCA10 F B C D E K )
            `
            ( NTP4VCShift ( NTP4VCA16 C N A ) x )
          )
          =/=
          0
          <->
          (
            ( NTP4VCA10 F B C D E K )
            `
            ( NTP4VCShift ( NTP4VCA8 C D E ) x )
          )
          =/=
          0
        )
      )
    ) $.

  ntp4vc-sched-group-cpus-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD H ( L ` x ) 1
      /\
      (
        NTP4VCValidRD H ( NTP4VCStorage C ( L ` x ) ) K
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < K
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( L ` x ) ) K
                  ( NTP4VCStorage C ( NTP4VCShift D y ) ) K
              )
            )
          )
      )
    ) $.

  ntp4vc-sched-group-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD H ( M ` x ) 1
      /\
      (
        NTP4VCValidRD H ( NTP4VCStorage C ( M ` x ) ) K
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < K
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( M ` x ) ) K
                  ( NTP4VCStorage C ( NTP4VCShift D y ) ) K
              )
            )
          )
      )
    ) $.

  ntp4vc-group-balance-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD H ( N ` x ) 1
      /\
      (
        NTP4VCValidRD H ( NTP4VCStorage C ( N ` x ) ) K
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < K
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( N ` x ) ) K
                  ( NTP4VCStorage C ( NTP4VCShift D y ) ) K
              )
            )
          )
      )
    ) $.

  ntp4vc-cpu-smt-mask-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < K
        ->
        (
          NTP4VCValidRD H ( O ` x ) 1
          /\
          (
            NTP4VCValidRD H ( NTP4VCStorage C ( O ` x ) ) K
            /\
            A. y e. ZZ
              (
                0 <_ y
                ->
                (
                  y < K
                  ->
                  (
                    NTP4VCSeparated
                      ( NTP4VCStorage C ( O ` x ) ) K
                      ( NTP4VCStorage C ( NTP4VCShift D y ) ) K
                  )
                )
              )
          )
        )
      )
    ) $.

  ntp4vc-should-we-balance-loop-inv-a2-established-goal16 $a |- (
    (
      ( NTP4VCA10 F B C D E K )
      `
      ( NTP4VCShift ( NTP4VCA8 C D E ) G )
    )
    =/=
    0
  ) $.
$}
