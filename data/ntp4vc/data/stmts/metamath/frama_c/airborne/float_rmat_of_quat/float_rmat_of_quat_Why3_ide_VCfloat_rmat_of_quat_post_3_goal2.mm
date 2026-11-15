$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/airborne/float_rmat_of_quat/float_rmat_of_quat_Why3_ide_VCfloat_rmat_of_quat_post_3_goal2:
  nine sequential real-memory writes construct a matrix from a unit
  quaternion, and the resulting matrix has determinant one under the
  generated memory-validity, linking, region, separation, and floating-point
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift implements the source address shift,
  NTP4VCRead applies a real-valued memory after a shift, and NTP4VCUpdate is
  functional update on the full address domain.

  NTP4VCQ0 through NTP4VCQ3 and NTP4VCR4 through NTP4VCR13 expand the
  source let-bindings. NTP4VCM0 through NTP4VCM8 preserve the nine functional
  updates in their source order, with every right-hand side evaluated from
  the original quaternion reads. The intermediate shift of the output
  address by zero is normalized using integer addition.

  The arbitrary integer-valued maps T and G represent the allocation and
  region functions. Membership of T in the arbitrary set L represents the
  source linked predicate. At the positive lengths 9 and 4, valid_rw,
  valid_rd, and separated are expanded into their exact base, offset,
  allocation-bound, and disjointness conditions. The source theory defines
  is_float32 as true and asserts is_finite32 for every real, so those
  hypotheses and the finite-value part of p_rvalid_floatquat disappear by
  bidirectional logical equivalence.

  NTP4VCSpecialOrthogonal expands p_special_orthogonal and l_determinant into
  the exact six-term determinant equation for the matrix read from the final
  updated memory. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no local $p proof declaration.
  Its imported set.mm dependency contains the standard library proofs.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCRead
  NTP4VCUpdate NTP4VCQ0 NTP4VCQ1 NTP4VCQ2 NTP4VCQ3
  NTP4VCR4 NTP4VCR5 NTP4VCR6 NTP4VCR7 NTP4VCR8 NTP4VCR9
  NTP4VCR10 NTP4VCR11 NTP4VCR12 NTP4VCR13
  NTP4VCM0 NTP4VCM1 NTP4VCM2 NTP4VCM3 NTP4VCM4
  NTP4VCM5 NTP4VCM6 NTP4VCM7 NTP4VCM8 NTP4VCSpecialOrthogonal
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-read-class $a class ( NTP4VCRead A B C ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-q0-class $a class ( NTP4VCQ0 A B ) $.
ntp4vc-q1-class $a class ( NTP4VCQ1 A B ) $.
ntp4vc-q2-class $a class ( NTP4VCQ2 A B ) $.
ntp4vc-q3-class $a class ( NTP4VCQ3 A B ) $.
ntp4vc-r4-class $a class ( NTP4VCR4 A B ) $.
ntp4vc-r5-class $a class ( NTP4VCR5 A B ) $.
ntp4vc-r6-class $a class ( NTP4VCR6 A B ) $.
ntp4vc-r7-class $a class ( NTP4VCR7 A B ) $.
ntp4vc-r8-class $a class ( NTP4VCR8 A B ) $.
ntp4vc-r9-class $a class ( NTP4VCR9 A B ) $.
ntp4vc-r10-class $a class ( NTP4VCR10 A B ) $.
ntp4vc-r11-class $a class ( NTP4VCR11 A B ) $.
ntp4vc-r12-class $a class ( NTP4VCR12 A B ) $.
ntp4vc-r13-class $a class ( NTP4VCR13 A B ) $.
ntp4vc-m0-class $a class ( NTP4VCM0 A B C ) $.
ntp4vc-m1-class $a class ( NTP4VCM1 A B C ) $.
ntp4vc-m2-class $a class ( NTP4VCM2 A B C ) $.
ntp4vc-m3-class $a class ( NTP4VCM3 A B C ) $.
ntp4vc-m4-class $a class ( NTP4VCM4 A B C ) $.
ntp4vc-m5-class $a class ( NTP4VCM5 A B C ) $.
ntp4vc-m6-class $a class ( NTP4VCM6 A B C ) $.
ntp4vc-m7-class $a class ( NTP4VCM7 A B C ) $.
ntp4vc-m8-class $a class ( NTP4VCM8 A B C ) $.
ntp4vc-special-orthogonal-syntax
  $a wff ( NTP4VCSpecialOrthogonal A B ) $.

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

ntp4vc-q0-def $a |- ( NTP4VCQ0 A B ) =
  ( NTP4VCRead A B 0 ) $.
ntp4vc-q1-def $a |- ( NTP4VCQ1 A B ) =
  ( NTP4VCRead A B 1 ) $.
ntp4vc-q2-def $a |- ( NTP4VCQ2 A B ) =
  ( NTP4VCRead A B 2 ) $.
ntp4vc-q3-def $a |- ( NTP4VCQ3 A B ) =
  ( NTP4VCRead A B 3 ) $.

ntp4vc-r4-def $a |- ( NTP4VCR4 A B ) =
  ( 2 x. ( NTP4VCQ0 A B ) ) $.
ntp4vc-r5-def $a |- ( NTP4VCR5 A B ) =
  ( 2 x. ( NTP4VCQ1 A B ) ) $.
ntp4vc-r6-def $a |- ( NTP4VCR6 A B ) =
  ( 2 x. ( NTP4VCQ3 A B ) ) $.
ntp4vc-r7-def $a |- ( NTP4VCR7 A B ) =
  ( ( NTP4VCR4 A B ) x. ( NTP4VCQ1 A B ) ) $.
ntp4vc-r8-def $a |- ( NTP4VCR8 A B ) =
  ( ( NTP4VCR4 A B ) x. ( NTP4VCQ2 A B ) ) $.
ntp4vc-r9-def $a |- ( NTP4VCR9 A B ) =
  ( ( NTP4VCR4 A B ) x. ( NTP4VCQ3 A B ) ) $.
ntp4vc-r10-def $a |- ( NTP4VCR10 A B ) =
  ( ( NTP4VCR5 A B ) x. ( NTP4VCQ2 A B ) ) $.
ntp4vc-r11-def $a |- ( NTP4VCR11 A B ) =
  ( ( NTP4VCR5 A B ) x. ( NTP4VCQ3 A B ) ) $.
ntp4vc-r12-def $a |- ( NTP4VCR12 A B ) =
  ( ( NTP4VCQ2 A B ) x. ( NTP4VCR6 A B ) ) $.
ntp4vc-r13-def $a |- ( NTP4VCR13 A B ) =
  ( ( ( NTP4VCR4 A B ) x. ( NTP4VCQ0 A B ) ) - 1 ) $.

ntp4vc-m0-def $a |- ( NTP4VCM0 A B C ) =
  ( NTP4VCUpdate
    A
    ( NTP4VCShift C 0 )
    (
      ( NTP4VCR13 A B )
      +
      ( ( NTP4VCR5 A B ) x. ( NTP4VCQ1 A B ) )
    )
  ) $.

ntp4vc-m1-def $a |- ( NTP4VCM1 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM0 A B C )
    ( NTP4VCShift C 1 )
    ( ( NTP4VCR10 A B ) + ( NTP4VCR9 A B ) )
  ) $.

ntp4vc-m2-def $a |- ( NTP4VCM2 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM1 A B C )
    ( NTP4VCShift C 2 )
    ( ( NTP4VCR11 A B ) - ( NTP4VCR8 A B ) )
  ) $.

ntp4vc-m3-def $a |- ( NTP4VCM3 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM2 A B C )
    ( NTP4VCShift C 3 )
    ( ( NTP4VCR10 A B ) - ( NTP4VCR9 A B ) )
  ) $.

ntp4vc-m4-def $a |- ( NTP4VCM4 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM3 A B C )
    ( NTP4VCShift C 4 )
    (
      ( NTP4VCR13 A B )
      +
      (
        ( 2 x. ( NTP4VCQ2 A B ) )
        x.
        ( NTP4VCQ2 A B )
      )
    )
  ) $.

ntp4vc-m5-def $a |- ( NTP4VCM5 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM4 A B C )
    ( NTP4VCShift C 5 )
    ( ( NTP4VCR12 A B ) + ( NTP4VCR7 A B ) )
  ) $.

ntp4vc-m6-def $a |- ( NTP4VCM6 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM5 A B C )
    ( NTP4VCShift C 6 )
    ( ( NTP4VCR11 A B ) + ( NTP4VCR8 A B ) )
  ) $.

ntp4vc-m7-def $a |- ( NTP4VCM7 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM6 A B C )
    ( NTP4VCShift C 7 )
    ( ( NTP4VCR12 A B ) - ( NTP4VCR7 A B ) )
  ) $.

ntp4vc-m8-def $a |- ( NTP4VCM8 A B C ) =
  ( NTP4VCUpdate
    ( NTP4VCM7 A B C )
    ( NTP4VCShift C 8 )
    (
      ( NTP4VCR13 A B )
      +
      ( ( NTP4VCR6 A B ) x. ( NTP4VCQ3 A B ) )
    )
  ) $.

ntp4vc-special-orthogonal-def $a |- (
  ( NTP4VCSpecialOrthogonal A B )
  <->
  (
    (
      (
        (
          (
            (
              (
                ( NTP4VCRead A B 0 )
                x.
                ( NTP4VCRead A B 4 )
              )
              x.
              ( NTP4VCRead A B 8 )
            )
            +
            (
              (
                ( NTP4VCRead A B 1 )
                x.
                ( NTP4VCRead A B 5 )
              )
              x.
              ( NTP4VCRead A B 6 )
            )
          )
          +
          (
            (
              ( NTP4VCRead A B 2 )
              x.
              ( NTP4VCRead A B 3 )
            )
            x.
            ( NTP4VCRead A B 7 )
          )
        )
        -
        (
          (
            ( NTP4VCRead A B 0 )
            x.
            ( NTP4VCRead A B 5 )
          )
          x.
          ( NTP4VCRead A B 7 )
        )
      )
      -
      (
        (
          ( NTP4VCRead A B 1 )
          x.
          ( NTP4VCRead A B 3 )
        )
        x.
        ( NTP4VCRead A B 8 )
      )
    )
    -
    (
      (
        ( NTP4VCRead A B 2 )
        x.
        ( NTP4VCRead A B 4 )
      )
      x.
      ( NTP4VCRead A B 6 )
    )
  )
  = 1
  )
) $.

${
  $d A B F G L T $.

  ntp4vc-input-address $e |- A e. NTP4VCAddr $.
  ntp4vc-output-address $e |- B e. NTP4VCAddr $.
  ntp4vc-real-memory $e |- F e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.

  ntp4vc-output-region $e |- (
    ( G ` ( NTP4VCBase B ) ) <_ 0
  ) $.
  ntp4vc-input-region $e |- (
    ( G ` ( NTP4VCBase A ) ) <_ 0
  ) $.
  ntp4vc-linked-allocation $e |- T e. L $.

  ntp4vc-unit-quaternion $e |- (
    (
      (
        (
          ( NTP4VCQ0 F A ) x. ( NTP4VCQ0 F A )
        )
        +
        (
          ( NTP4VCQ1 F A ) x. ( NTP4VCQ1 F A )
        )
      )
      +
      (
        ( NTP4VCQ2 F A ) x. ( NTP4VCQ2 F A )
      )
    )
    +
    (
      ( NTP4VCQ3 F A ) x. ( NTP4VCQ3 F A )
    )
    = 1
  ) $.

  ntp4vc-output-positive-base $e |- 0 < ( NTP4VCBase B ) $.
  ntp4vc-output-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset B )
  ) $.
  ntp4vc-output-valid-end $e |- (
    ( ( NTP4VCOffset B ) + 9 ) <_ ( T ` ( NTP4VCBase B ) )
  ) $.

  ntp4vc-input-nonzero-base $e |- ( NTP4VCBase A ) =/= 0 $.
  ntp4vc-input-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset A )
  ) $.
  ntp4vc-input-valid-end $e |- (
    ( ( NTP4VCOffset A ) + 4 ) <_ ( T ` ( NTP4VCBase A ) )
  ) $.

  ntp4vc-separated $e |- (
    (
      ( NTP4VCBase B ) =/= ( NTP4VCBase A )
      \/
      ( ( NTP4VCOffset A ) + 4 ) <_ ( NTP4VCOffset B )
    )
    \/
    ( ( NTP4VCOffset B ) + 9 ) <_ ( NTP4VCOffset A )
  ) $.

  ntp4vc-float-rmat-of-quat-post-3-goal2 $a |- (
    NTP4VCSpecialOrthogonal ( NTP4VCM8 F A B ) B
  ) $.
$}
