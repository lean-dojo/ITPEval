$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/airborne/float_rmat_vmult/float_rmat_vmult_Why3_ide_VCfloat_rmat_vmult_post_goal0:
  three sequential real-memory writes compute the product of a 3-by-3 real
  matrix with a three-component vector under the generated memory-validity,
  linking, region, separation, and floating-point assumptions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift implements the source address shift,
  NTP4VCRead applies a real-valued memory function after a shift, and
  NTP4VCUpdate is functional update on the full address domain.

  NTP4VCM0 through NTP4VCM2 preserve the source's three functional updates in
  order. Every right-hand-side matrix and vector read is taken from the
  immediately preceding memory, exactly as in the verification condition.
  The source's intermediate shifts by zero are normalized by integer
  addition.

  The arbitrary integer-valued maps T and G represent the source allocation
  and region functions. Membership of T in the arbitrary set L represents
  the source linked predicate. At the positive lengths 3 and 9, valid_rw,
  valid_rd, and separated are expanded into their exact base, offset,
  allocation-bound, and disjointness conditions. The source defines
  is_float32 as true and its imported theory asserts is_finite32 for every
  real, so those hypotheses disappear by bidirectional logical equivalence.

  The conclusion expands the source vector-record equality and ordinary
  matrix-vector multiplication into three real component equations, with all
  output, matrix, and vector reads taken from NTP4VCM2. The final declaration
  is Metamath's native unproved $a statement encoding; this database contains
  no local $p proof declaration. Its imported set.mm dependency contains the
  standard library proofs.
$)

$c NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCRead
  NTP4VCUpdate NTP4VCM0 NTP4VCM1 NTP4VCM2 $.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-read-class $a class ( NTP4VCRead A B C ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-m0-class $a class ( NTP4VCM0 A B C D ) $.
ntp4vc-m1-class $a class ( NTP4VCM1 A B C D ) $.
ntp4vc-m2-class $a class ( NTP4VCM2 A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-read-def $a |- ( NTP4VCRead A B C ) =
  ( A ` ( NTP4VCShift B C ) ) $.

${
  $d x A $.  $d x B $.  $d x C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    ( x e. NTP4VCAddr |-> if ( x = B , C , ( A ` x ) ) ) $.
$}

ntp4vc-m0-def $a |- ( NTP4VCM0 A B C D ) =
  ( NTP4VCUpdate
    A
    ( NTP4VCShift B 0 )
    (
      (
        (
          ( NTP4VCRead A D 0 )
          x.
          ( NTP4VCRead A C 0 )
        )
        +
        (
          ( NTP4VCRead A D 1 )
          x.
          ( NTP4VCRead A C 1 )
        )
      )
      +
      (
        ( NTP4VCRead A D 2 )
        x.
        ( NTP4VCRead A C 2 )
      )
    )
  ) $.

ntp4vc-m1-def $a |- ( NTP4VCM1 A B C D ) =
  ( NTP4VCUpdate
    ( NTP4VCM0 A B C D )
    ( NTP4VCShift B 1 )
    (
      (
        (
          ( NTP4VCRead ( NTP4VCM0 A B C D ) D 3 )
          x.
          ( NTP4VCRead ( NTP4VCM0 A B C D ) C 0 )
        )
        +
        (
          ( NTP4VCRead ( NTP4VCM0 A B C D ) D 4 )
          x.
          ( NTP4VCRead ( NTP4VCM0 A B C D ) C 1 )
        )
      )
      +
      (
        ( NTP4VCRead ( NTP4VCM0 A B C D ) D 5 )
        x.
        ( NTP4VCRead ( NTP4VCM0 A B C D ) C 2 )
      )
    )
  ) $.

ntp4vc-m2-def $a |- ( NTP4VCM2 A B C D ) =
  ( NTP4VCUpdate
    ( NTP4VCM1 A B C D )
    ( NTP4VCShift B 2 )
    (
      (
        (
          ( NTP4VCRead ( NTP4VCM1 A B C D ) D 6 )
          x.
          ( NTP4VCRead ( NTP4VCM1 A B C D ) C 0 )
        )
        +
        (
          ( NTP4VCRead ( NTP4VCM1 A B C D ) D 7 )
          x.
          ( NTP4VCRead ( NTP4VCM1 A B C D ) C 1 )
        )
      )
      +
      (
        ( NTP4VCRead ( NTP4VCM1 A B C D ) D 8 )
        x.
        ( NTP4VCRead ( NTP4VCM1 A B C D ) C 2 )
      )
    )
  ) $.

${
  $d F G L P R T V $.

  ntp4vc-output-address $e |- P e. NTP4VCAddr $.
  ntp4vc-vector-address $e |- V e. NTP4VCAddr $.
  ntp4vc-matrix-address $e |- R e. NTP4VCAddr $.
  ntp4vc-real-memory $e |- F e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.

  ntp4vc-output-region $e |- (
    ( G ` ( NTP4VCBase P ) ) <_ 0
  ) $.
  ntp4vc-vector-region $e |- (
    ( G ` ( NTP4VCBase V ) ) <_ 0
  ) $.
  ntp4vc-matrix-region $e |- (
    ( G ` ( NTP4VCBase R ) ) <_ 0
  ) $.
  ntp4vc-linked-allocation $e |- T e. L $.

  ntp4vc-output-positive-base $e |- 0 < ( NTP4VCBase P ) $.
  ntp4vc-output-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset P )
  ) $.
  ntp4vc-output-valid-end $e |- (
    ( ( NTP4VCOffset P ) + 3 ) <_ ( T ` ( NTP4VCBase P ) )
  ) $.

  ntp4vc-vector-nonzero-base $e |- ( NTP4VCBase V ) =/= 0 $.
  ntp4vc-vector-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset V )
  ) $.
  ntp4vc-vector-valid-end $e |- (
    ( ( NTP4VCOffset V ) + 3 ) <_ ( T ` ( NTP4VCBase V ) )
  ) $.

  ntp4vc-matrix-nonzero-base $e |- ( NTP4VCBase R ) =/= 0 $.
  ntp4vc-matrix-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset R )
  ) $.
  ntp4vc-matrix-valid-end $e |- (
    ( ( NTP4VCOffset R ) + 9 ) <_ ( T ` ( NTP4VCBase R ) )
  ) $.

  ntp4vc-output-vector-separated $e |- (
    (
      ( NTP4VCBase P ) =/= ( NTP4VCBase V )
      \/
      ( ( NTP4VCOffset V ) + 3 ) <_ ( NTP4VCOffset P )
    )
    \/
    ( ( NTP4VCOffset P ) + 3 ) <_ ( NTP4VCOffset V )
  ) $.

  ntp4vc-output-matrix-separated $e |- (
    (
      ( NTP4VCBase P ) =/= ( NTP4VCBase R )
      \/
      ( ( NTP4VCOffset R ) + 9 ) <_ ( NTP4VCOffset P )
    )
    \/
    ( ( NTP4VCOffset P ) + 3 ) <_ ( NTP4VCOffset R )
  ) $.

  ntp4vc-vector-matrix-separated $e |- (
    (
      ( NTP4VCBase V ) =/= ( NTP4VCBase R )
      \/
      ( ( NTP4VCOffset R ) + 9 ) <_ ( NTP4VCOffset V )
    )
    \/
    ( ( NTP4VCOffset V ) + 3 ) <_ ( NTP4VCOffset R )
  ) $.

  ntp4vc-float-rmat-vmult-post-goal0 $a |- (
    (
      (
        (
          ( NTP4VCRead ( NTP4VCM2 F P V R ) R 0 )
          x.
          ( NTP4VCRead ( NTP4VCM2 F P V R ) V 0 )
        )
        +
        (
          ( NTP4VCRead ( NTP4VCM2 F P V R ) R 1 )
          x.
          ( NTP4VCRead ( NTP4VCM2 F P V R ) V 1 )
        )
      )
      +
      (
        ( NTP4VCRead ( NTP4VCM2 F P V R ) R 2 )
        x.
        ( NTP4VCRead ( NTP4VCM2 F P V R ) V 2 )
      )
    )
    =
    ( NTP4VCRead ( NTP4VCM2 F P V R ) P 0 )
    /\
    (
      (
        (
          (
            ( NTP4VCRead ( NTP4VCM2 F P V R ) R 3 )
            x.
            ( NTP4VCRead ( NTP4VCM2 F P V R ) V 0 )
          )
          +
          (
            ( NTP4VCRead ( NTP4VCM2 F P V R ) R 4 )
            x.
            ( NTP4VCRead ( NTP4VCM2 F P V R ) V 1 )
          )
        )
        +
        (
          ( NTP4VCRead ( NTP4VCM2 F P V R ) R 5 )
          x.
          ( NTP4VCRead ( NTP4VCM2 F P V R ) V 2 )
        )
      )
      =
      ( NTP4VCRead ( NTP4VCM2 F P V R ) P 1 )
      /\
      (
        (
          (
            (
              ( NTP4VCRead ( NTP4VCM2 F P V R ) R 6 )
              x.
              ( NTP4VCRead ( NTP4VCM2 F P V R ) V 0 )
            )
            +
            (
              ( NTP4VCRead ( NTP4VCM2 F P V R ) R 7 )
              x.
              ( NTP4VCRead ( NTP4VCM2 F P V R ) V 1 )
            )
          )
          +
          (
            ( NTP4VCRead ( NTP4VCM2 F P V R ) R 8 )
            x.
            ( NTP4VCRead ( NTP4VCM2 F P V R ) V 2 )
          )
        )
        =
        ( NTP4VCRead ( NTP4VCM2 F P V R ) P 2 )
      )
    )
  ) $.
$}
