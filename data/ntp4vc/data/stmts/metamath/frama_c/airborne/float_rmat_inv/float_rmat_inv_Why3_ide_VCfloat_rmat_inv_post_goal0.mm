$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/airborne/float_rmat_inv/float_rmat_inv_Why3_ide_VCfloat_rmat_inv_post_goal0:
  nine sequential real-memory writes copy a 3-by-3 matrix into a separate
  writable block in transposed order under the generated memory-safety,
  linking, region, and separation conditions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source address structure is represented exactly by ZZ X. ZZ, with base
  and offset given by 1st and 2nd. NTP4VCShift implements the source shift,
  NTP4VCRead applies a real-valued memory function after a shift, and
  NTP4VCUpdate is functional update on the full address domain.

  NTP4VCM0 through NTP4VCM8 preserve the source's nine updates in order. Each
  right-hand-side read is taken from the immediately preceding memory, exactly
  as in the verification condition. Nested zero shifts in the source lets are
  normalized using integer addition.

  The arbitrary integer-valued maps T and G represent the source allocation
  and region functions. Membership of T in the arbitrary set L represents the
  source linked predicate. At the positive length 9, valid_rw, valid_rd, and
  separated are expanded into their exact base, offset, allocation-bound, and
  disjointness conditions. The source theory asserts is_finite32 for every
  real, so the nine finite-value conjuncts in p_rvalid_floatrmat disappear by
  bidirectional logical equivalence.

  The conclusion expands the source record equality after transpose into its
  nine real component equations, with both matrices read from NTP4VCM8. The
  final declaration is Metamath's native unproved $a statement encoding; this
  file contains no local $p proof declaration. Its imported set.mm dependency
  contains the standard library proofs.
$)

$c NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCRead
  NTP4VCUpdate NTP4VCM0 NTP4VCM1 NTP4VCM2 NTP4VCM3 NTP4VCM4
  NTP4VCM5 NTP4VCM6 NTP4VCM7 NTP4VCM8 $.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-read-class $a class ( NTP4VCRead A B C ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-m0-class $a class ( NTP4VCM0 A B C ) $.
ntp4vc-m1-class $a class ( NTP4VCM1 A B C ) $.
ntp4vc-m2-class $a class ( NTP4VCM2 A B C ) $.
ntp4vc-m3-class $a class ( NTP4VCM3 A B C ) $.
ntp4vc-m4-class $a class ( NTP4VCM4 A B C ) $.
ntp4vc-m5-class $a class ( NTP4VCM5 A B C ) $.
ntp4vc-m6-class $a class ( NTP4VCM6 A B C ) $.
ntp4vc-m7-class $a class ( NTP4VCM7 A B C ) $.
ntp4vc-m8-class $a class ( NTP4VCM8 A B C ) $.

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

ntp4vc-m0-def $a |- ( NTP4VCM0 A B C ) =
  ( NTP4VCUpdate
    A
    ( NTP4VCShift B 0 )
    ( NTP4VCRead A C 0 )
  ) $.

ntp4vc-m1-def $a |- ( NTP4VCM1 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM0 A B C )
    ( NTP4VCShift B 1 )
    ( NTP4VCRead ( NTP4VCM0 A B C ) C 3 )
  ) $.

ntp4vc-m2-def $a |- ( NTP4VCM2 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM1 A B C )
    ( NTP4VCShift B 2 )
    ( NTP4VCRead ( NTP4VCM1 A B C ) C 6 )
  ) $.

ntp4vc-m3-def $a |- ( NTP4VCM3 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM2 A B C )
    ( NTP4VCShift B 3 )
    ( NTP4VCRead ( NTP4VCM2 A B C ) C 1 )
  ) $.

ntp4vc-m4-def $a |- ( NTP4VCM4 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM3 A B C )
    ( NTP4VCShift B 4 )
    ( NTP4VCRead ( NTP4VCM3 A B C ) C 4 )
  ) $.

ntp4vc-m5-def $a |- ( NTP4VCM5 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM4 A B C )
    ( NTP4VCShift B 5 )
    ( NTP4VCRead ( NTP4VCM4 A B C ) C 7 )
  ) $.

ntp4vc-m6-def $a |- ( NTP4VCM6 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM5 A B C )
    ( NTP4VCShift B 6 )
    ( NTP4VCRead ( NTP4VCM5 A B C ) C 2 )
  ) $.

ntp4vc-m7-def $a |- ( NTP4VCM7 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM6 A B C )
    ( NTP4VCShift B 7 )
    ( NTP4VCRead ( NTP4VCM6 A B C ) C 5 )
  ) $.

ntp4vc-m8-def $a |- ( NTP4VCM8 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM7 A B C )
    ( NTP4VCShift B 8 )
    ( NTP4VCRead ( NTP4VCM7 A B C ) C 8 )
  ) $.

${
  $d A B F G L T $.

  ntp4vc-output-address $e |- A e. NTP4VCAddr $.
  ntp4vc-input-address $e |- B e. NTP4VCAddr $.
  ntp4vc-real-memory $e |- F e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.

  ntp4vc-output-region $e |- (
    ( G ` ( NTP4VCBase A ) ) <_ 0
  ) $.
  ntp4vc-input-region $e |- (
    ( G ` ( NTP4VCBase B ) ) <_ 0
  ) $.
  ntp4vc-linked-allocation $e |- T e. L $.

  ntp4vc-output-positive-base $e |- 0 < ( NTP4VCBase A ) $.
  ntp4vc-output-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset A )
  ) $.
  ntp4vc-output-valid-end $e |- (
    ( ( NTP4VCOffset A ) + 9 ) <_ ( T ` ( NTP4VCBase A ) )
  ) $.

  ntp4vc-input-nonzero-base $e |- ( NTP4VCBase B ) =/= 0 $.
  ntp4vc-input-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset B )
  ) $.
  ntp4vc-input-valid-end $e |- (
    ( ( NTP4VCOffset B ) + 9 ) <_ ( T ` ( NTP4VCBase B ) )
  ) $.

  ntp4vc-separated $e |- (
    (
      ( NTP4VCBase A ) =/= ( NTP4VCBase B )
      \/
      ( ( NTP4VCOffset B ) + 9 ) <_ ( NTP4VCOffset A )
    )
    \/
    ( ( NTP4VCOffset A ) + 9 ) <_ ( NTP4VCOffset B )
  ) $.

  ntp4vc-float-rmat-inv-post-goal0 $a |- (
    (
      ( NTP4VCRead ( NTP4VCM8 F A B ) A 0 )
      =
      ( NTP4VCRead ( NTP4VCM8 F A B ) B 0 )
    )
    /\
    (
      (
        ( NTP4VCRead ( NTP4VCM8 F A B ) A 1 )
        =
        ( NTP4VCRead ( NTP4VCM8 F A B ) B 3 )
      )
      /\
      (
        (
          ( NTP4VCRead ( NTP4VCM8 F A B ) A 2 )
          =
          ( NTP4VCRead ( NTP4VCM8 F A B ) B 6 )
        )
        /\
        (
          (
            ( NTP4VCRead ( NTP4VCM8 F A B ) A 3 )
            =
            ( NTP4VCRead ( NTP4VCM8 F A B ) B 1 )
          )
          /\
          (
            (
              ( NTP4VCRead ( NTP4VCM8 F A B ) A 4 )
              =
              ( NTP4VCRead ( NTP4VCM8 F A B ) B 4 )
            )
            /\
            (
              (
                ( NTP4VCRead ( NTP4VCM8 F A B ) A 5 )
                =
                ( NTP4VCRead ( NTP4VCM8 F A B ) B 7 )
              )
              /\
              (
                (
                  ( NTP4VCRead ( NTP4VCM8 F A B ) A 6 )
                  =
                  ( NTP4VCRead ( NTP4VCM8 F A B ) B 2 )
                )
                /\
                (
                  (
                    ( NTP4VCRead ( NTP4VCM8 F A B ) A 7 )
                    =
                    ( NTP4VCRead ( NTP4VCM8 F A B ) B 5 )
                  )
                  /\
                  (
                    ( NTP4VCRead ( NTP4VCM8 F A B ) A 8 )
                    =
                    ( NTP4VCRead ( NTP4VCM8 F A B ) B 8 )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}
