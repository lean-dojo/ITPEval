$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/reverse/reverse_Why3_ide_VCreverse_loop_inv_right_preserved_goal7:
  the reverse-loop verification condition preserves the right-hand reversal
  invariant after swapping the two indexed memory cells, under the generated
  arithmetic, memory-validity, integer-range, framing, and reversal
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ. NTP4VCShift,
  NTP4VCSeparated, NTP4VCHavoc, NTP4VCUpdate, NTP4VCValidRW,
  NTP4VCUint32, NTP4VCSint32, NTP4VCUnchanged, and NTP4VCReverse4
  directly expand the corresponding source definitions. In particular,
  havoc and update are full-domain functions, and both quantified predicates
  retain their unrestricted integer domains.

  NTP4VCTDiv is integer division truncated toward zero. This follows the Lean
  and Isabelle ground-truth statements; the Rocq rendering's isolated use of
  remainder in the corresponding let-bound term is treated as a transcription
  discrepancy. The arbitrary function H represents Memory.region, membership
  of G in the arbitrary set I represents Memory.linked, and J represents
  Cint.to_uint32 with its source-theory range and identity laws. The named
  NTP4VCA1 through NTP4VCA8 and NTP4VCX1 through NTP4VCX4 terms are exact
  expansions of the source let bindings. The final declaration is Metamath's
  native unproved $a statement encoding; this database adds no $p proof.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc NTP4VCUpdate NTP4VCTDiv
  NTP4VCMaxIndex NTP4VCMaxUint32 NTP4VCUint32Limit
  NTP4VCSint32Limit NTP4VCValidRW NTP4VCUint32 NTP4VCSint32
  NTP4VCUnchanged NTP4VCReverse4
  NTP4VCA1 NTP4VCA2 NTP4VCX1 NTP4VCA3 NTP4VCA4 NTP4VCA5
  NTP4VCA6 NTP4VCA7 NTP4VCA8 NTP4VCX2 NTP4VCX3 NTP4VCX4
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-max-uint32-class $a class NTP4VCMaxUint32 $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.

ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C D ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B C ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B C D E ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B C D E F ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B C D E F ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B C D E ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A B ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-reverse4-syntax
  $a wff ( NTP4VCReverse4 A B C D E F ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

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

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if
  (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
  ) $.

ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4 $.
ntp4vc-max-uint32-def $a |- NTP4VCMaxUint32 =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

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

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

${
  $d x A B C D E $.
  ntp4vc-unchanged-def $a |- (
    ( NTP4VCUnchanged A B C D E )
    <->
    A. x e. ZZ
      (
        D <_ x
        ->
        (
          x < E
          ->
          (
            ( B ` ( NTP4VCShift C x ) )
            =
            ( A ` ( NTP4VCShift C x ) )
          )
        )
      )
  ) $.
$}

${
  $d x A B C D E F $.
  ntp4vc-reverse4-def $a |- (
    ( NTP4VCReverse4 A B C D E F )
    <->
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x < ( E - D )
          ->
          (
            (
              A
              `
              (
                NTP4VCShift
                  ( NTP4VCShift C F )
                  ( ( ( E - D ) - 1 ) - x )
              )
            )
            =
            (
              B
              `
              ( NTP4VCShift ( NTP4VCShift C D ) x )
            )
          )
        )
      )
  ) $.
$}

ntp4vc-a1-def $a |- ( NTP4VCA1 A ) =
  ( NTP4VCShift A 0 ) $.

ntp4vc-a2-def $a |- ( NTP4VCA2 A B C D ) =
  ( NTP4VCHavoc B C ( NTP4VCA1 A ) D ) $.

ntp4vc-x1-def $a |- ( NTP4VCX1 A B ) =
  ( ( A - 1 ) - B ) $.

ntp4vc-a3-def $a |- ( NTP4VCA3 A B C ) =
  ( NTP4VCShift A ( NTP4VCX1 B C ) ) $.

ntp4vc-a4-def $a |- ( NTP4VCA4 A B ) =
  ( NTP4VCShift A B ) $.

ntp4vc-a5-def $a |- ( NTP4VCA5 A B C D E ) =
  (
    ( NTP4VCA2 A B C D )
    `
    ( NTP4VCA3 A D E )
  ) $.

ntp4vc-a6-def $a |- ( NTP4VCA6 A B C D E F ) =
  (
    NTP4VCUpdate
      (
        NTP4VCUpdate
          ( NTP4VCA2 A B C D )
          ( NTP4VCA3 A D E )
          F
      )
      ( NTP4VCA4 A E )
      ( NTP4VCA5 A B C D E )
  ) $.

ntp4vc-a7-def $a |- ( NTP4VCA7 A B C D E F ) =
  (
    ( NTP4VCA6 A B C D E F )
    `
    ( NTP4VCA3 A D E )
  ) $.

ntp4vc-a8-def $a |- ( NTP4VCA8 A B C D E ) =
  (
    ( NTP4VCA2 A B C D )
    `
    ( NTP4VCA4 A E )
  ) $.

ntp4vc-x2-def $a |- ( NTP4VCX2 A ) =
  ( NTP4VCTDiv A 2 ) $.

ntp4vc-x3-def $a |- ( NTP4VCX3 A B ) =
  ( A ` ( B - 1 ) ) $.

ntp4vc-x4-def $a |- ( NTP4VCX4 A B ) =
  ( A - B ) $.

${
  $d x A B C D E F G H I J $.

  ntp4vc-a-type $e |- A e. NTP4VCAddr $.
  ntp4vc-t1-type $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-type $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-type $e |- D e. ZZ $.
  ntp4vc-i2-type $e |- E e. ZZ $.
  ntp4vc-i-type $e |- F e. ZZ $.
  ntp4vc-t-type $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-type $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-type $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-type $e |- J e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( J ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( J ` x ) = x ) $.

  ntp4vc-a7-a8 $e |- (
    ( NTP4VCA7 A B C D E F )
    =
    ( NTP4VCA8 A B C D E )
  ) $.
  ntp4vc-i1-positive $e |- 0 < D $.
  ntp4vc-i2-nonnegative $e |- 0 <_ E $.
  ntp4vc-i2-lt-x2 $e |- E < ( NTP4VCX2 D ) $.
  ntp4vc-i2-le-x2 $e |- E <_ ( NTP4VCX2 D ) $.
  ntp4vc-region-base $e |- ( H ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-i2-plus-x2 $e |- ( E + ( NTP4VCX2 D ) ) <_ D $.
  ntp4vc-i2-le-x3 $e |- E <_ ( NTP4VCX3 J D ) $.
  ntp4vc-i2-max-index $e |- E <_ NTP4VCMaxIndex $.
  ntp4vc-x3-max $e |- (
    ( NTP4VCX3 J D )
    <_
    ( NTP4VCMaxUint32 + E )
  ) $.
  ntp4vc-linked $e |- G e. I $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-x2-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX2 D ) ) $.
  ntp4vc-i2-next-uint32 $e |- ( NTP4VCUint32 ( 1 + E ) ) $.
  ntp4vc-a1-valid $e |- (
    NTP4VCValidRW G ( NTP4VCA1 A ) D
  ) $.
  ntp4vc-a4-valid $e |- (
    NTP4VCValidRW G ( NTP4VCA4 A E ) 1
  ) $.
  ntp4vc-a8-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA8 A B C D E )
  ) $.
  ntp4vc-a5-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA5 A B C D E )
  ) $.
  ntp4vc-a3-valid $e |- (
    NTP4VCValidRW G ( NTP4VCA3 A D E ) 1
  ) $.
  ntp4vc-a7-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA7 A B C D E F )
  ) $.
  ntp4vc-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA2 A B C D )
      C
      A
      E
      ( NTP4VCX4 D E )
  ) $.
  ntp4vc-reverse-left $e |- (
    NTP4VCReverse4
      ( NTP4VCA2 A B C D )
      C
      A
      0
      E
      ( NTP4VCX4 D E )
  ) $.
  ntp4vc-reverse-right $e |- (
    NTP4VCReverse4
      ( NTP4VCA2 A B C D )
      C
      A
      ( NTP4VCX4 D E )
      D
      0
  ) $.

  ntp4vc-reverse-loop-inv-right-preserved-goal7 $a |- (
    NTP4VCReverse4
      ( NTP4VCA6 A B C D E F )
      C
      A
      ( NTP4VCX1 D E )
      D
      0
  ) $.
$}
