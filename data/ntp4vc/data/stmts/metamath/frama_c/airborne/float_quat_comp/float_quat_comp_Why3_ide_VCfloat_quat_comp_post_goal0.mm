$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/airborne/float_quat_comp/float_quat_comp_Why3_ide_VCfloat_quat_comp_post_goal0:
  the four memory writes performed by floating-point quaternion composition
  agree with real quaternion multiplication under the generated memory-safety
  and separation conditions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source address structure is represented exactly by ZZ X. ZZ, with base
  and offset given by 1st and 2nd. NTP4VCShift implements the source shift
  operation, and NTP4VCRead applies a real-valued memory function after that
  shift. The allocation map T and region map G are arbitrary integer-valued
  functions. L is an arbitrary set of allocation maps and therefore faithfully
  represents the source's otherwise-unconstrained linked predicate.

  The source definitions make is_float32 identically True. Its thirty-two
  hypotheses therefore disappear by definitional equivalence. Likewise,
  is_finite32 holds for every real in the source theory, so each
  p_rvalid_floatquat hypothesis reduces to the displayed valid-read bounds.
  valid_rw and valid_rd are expanded at the positive length 4.

  NTP4VCUpdate is the source's functional memory update. NTP4VCM0 through
  NTP4VCM3 encode the four writes successively, with every right-hand-side read
  taken from the preceding memory exactly as in the verification condition.
  The final conjunction expands the real-vector/quaternion equality, with every
  component on both sides read from NTP4VCM3. It preserves the multiplication
  order: the quaternion at S is multiplied on the left by the quaternion at Q.

  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c NTP4VCAddr NTP4VCShift NTP4VCRead NTP4VCBase NTP4VCOffset
  NTP4VCUpdate NTP4VCM0 NTP4VCM1 NTP4VCM2 NTP4VCM3 $.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-read-class $a class ( NTP4VCRead A B C ) $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-m0-class $a class ( NTP4VCM0 A B C D ) $.
ntp4vc-m1-class $a class ( NTP4VCM1 A B C D ) $.
ntp4vc-m2-class $a class ( NTP4VCM2 A B C D ) $.
ntp4vc-m3-class $a class ( NTP4VCM3 A B C D ) $.

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
          ( ( NTP4VCRead A D 0 ) x. ( NTP4VCRead A C 0 ) )
          -
          ( ( NTP4VCRead A D 1 ) x. ( NTP4VCRead A C 1 ) )
        )
        -
        ( ( NTP4VCRead A D 2 ) x. ( NTP4VCRead A C 2 ) )
      )
      -
      ( ( NTP4VCRead A D 3 ) x. ( NTP4VCRead A C 3 ) )
    )
  ) $.

ntp4vc-m1-def $a |- ( NTP4VCM1 A B C D ) =
  ( NTP4VCUpdate
    ( NTP4VCM0 A B C D )
    ( NTP4VCShift B 1 )
    (
      (
        (
          (
            ( NTP4VCRead ( NTP4VCM0 A B C D ) D 0 )
            x.
            ( NTP4VCRead ( NTP4VCM0 A B C D ) C 1 )
          )
          +
          (
            ( NTP4VCRead ( NTP4VCM0 A B C D ) D 1 )
            x.
            ( NTP4VCRead ( NTP4VCM0 A B C D ) C 0 )
          )
        )
        +
        (
          ( NTP4VCRead ( NTP4VCM0 A B C D ) D 2 )
          x.
          ( NTP4VCRead ( NTP4VCM0 A B C D ) C 3 )
        )
      )
      -
      (
        ( NTP4VCRead ( NTP4VCM0 A B C D ) D 3 )
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
          (
            ( NTP4VCRead ( NTP4VCM1 A B C D ) D 0 )
            x.
            ( NTP4VCRead ( NTP4VCM1 A B C D ) C 2 )
          )
          -
          (
            ( NTP4VCRead ( NTP4VCM1 A B C D ) D 1 )
            x.
            ( NTP4VCRead ( NTP4VCM1 A B C D ) C 3 )
          )
        )
        +
        (
          ( NTP4VCRead ( NTP4VCM1 A B C D ) D 2 )
          x.
          ( NTP4VCRead ( NTP4VCM1 A B C D ) C 0 )
        )
      )
      +
      (
        ( NTP4VCRead ( NTP4VCM1 A B C D ) D 3 )
        x.
        ( NTP4VCRead ( NTP4VCM1 A B C D ) C 1 )
      )
    )
  ) $.

ntp4vc-m3-def $a |- ( NTP4VCM3 A B C D ) =
  ( NTP4VCUpdate
    ( NTP4VCM2 A B C D )
    ( NTP4VCShift B 3 )
    (
      (
        (
          (
            ( NTP4VCRead ( NTP4VCM2 A B C D ) D 0 )
            x.
            ( NTP4VCRead ( NTP4VCM2 A B C D ) C 3 )
          )
          +
          (
            ( NTP4VCRead ( NTP4VCM2 A B C D ) D 1 )
            x.
            ( NTP4VCRead ( NTP4VCM2 A B C D ) C 2 )
          )
        )
        -
        (
          ( NTP4VCRead ( NTP4VCM2 A B C D ) D 2 )
          x.
          ( NTP4VCRead ( NTP4VCM2 A B C D ) C 1 )
        )
      )
      +
      (
        ( NTP4VCRead ( NTP4VCM2 A B C D ) D 3 )
        x.
        ( NTP4VCRead ( NTP4VCM2 A B C D ) C 0 )
      )
    )
  ) $.

${
  $d F G L P Q S T $.

  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-output-address $e |- P e. NTP4VCAddr $.
  ntp4vc-right-address $e |- Q e. NTP4VCAddr $.
  ntp4vc-left-address $e |- S e. NTP4VCAddr $.
  ntp4vc-real-memory $e |- F e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.

  sep-a3-a4 $e |- ( NTP4VCShift P 0 ) =/= ( NTP4VCShift Q 0 ) $.
  sep-a5-a4 $e |- ( NTP4VCShift S 0 ) =/= ( NTP4VCShift Q 0 ) $.
  sep-a5-a3 $e |- ( NTP4VCShift S 0 ) =/= ( NTP4VCShift P 0 ) $.
  sep-a6-a3 $e |- ( NTP4VCShift Q 1 ) =/= ( NTP4VCShift P 0 ) $.
  sep-a6-a5 $e |- ( NTP4VCShift Q 1 ) =/= ( NTP4VCShift S 0 ) $.
  sep-a7-a4 $e |- ( NTP4VCShift P 1 ) =/= ( NTP4VCShift Q 0 ) $.
  sep-a7-a5 $e |- ( NTP4VCShift P 1 ) =/= ( NTP4VCShift S 0 ) $.
  sep-a7-a6 $e |- ( NTP4VCShift P 1 ) =/= ( NTP4VCShift Q 1 ) $.
  sep-a8-a4 $e |- ( NTP4VCShift S 1 ) =/= ( NTP4VCShift Q 0 ) $.
  sep-a8-a3 $e |- ( NTP4VCShift S 1 ) =/= ( NTP4VCShift P 0 ) $.
  sep-a8-a6 $e |- ( NTP4VCShift S 1 ) =/= ( NTP4VCShift Q 1 ) $.
  sep-a8-a7 $e |- ( NTP4VCShift S 1 ) =/= ( NTP4VCShift P 1 ) $.
  sep-a9-a3 $e |- ( NTP4VCShift Q 2 ) =/= ( NTP4VCShift P 0 ) $.
  sep-a9-a5 $e |- ( NTP4VCShift Q 2 ) =/= ( NTP4VCShift S 0 ) $.
  sep-a9-a7 $e |- ( NTP4VCShift Q 2 ) =/= ( NTP4VCShift P 1 ) $.
  sep-a9-a8 $e |- ( NTP4VCShift Q 2 ) =/= ( NTP4VCShift S 1 ) $.
  sep-a10-a4 $e |- ( NTP4VCShift P 2 ) =/= ( NTP4VCShift Q 0 ) $.
  sep-a10-a5 $e |- ( NTP4VCShift P 2 ) =/= ( NTP4VCShift S 0 ) $.
  sep-a10-a6 $e |- ( NTP4VCShift P 2 ) =/= ( NTP4VCShift Q 1 ) $.
  sep-a10-a8 $e |- ( NTP4VCShift P 2 ) =/= ( NTP4VCShift S 1 ) $.
  sep-a10-a9 $e |- ( NTP4VCShift P 2 ) =/= ( NTP4VCShift Q 2 ) $.
  sep-a11-a4 $e |- ( NTP4VCShift S 2 ) =/= ( NTP4VCShift Q 0 ) $.
  sep-a11-a3 $e |- ( NTP4VCShift S 2 ) =/= ( NTP4VCShift P 0 ) $.
  sep-a11-a6 $e |- ( NTP4VCShift S 2 ) =/= ( NTP4VCShift Q 1 ) $.
  sep-a11-a7 $e |- ( NTP4VCShift S 2 ) =/= ( NTP4VCShift P 1 ) $.
  sep-a11-a9 $e |- ( NTP4VCShift S 2 ) =/= ( NTP4VCShift Q 2 ) $.
  sep-a11-a10 $e |- ( NTP4VCShift S 2 ) =/= ( NTP4VCShift P 2 ) $.
  sep-a12-a3 $e |- ( NTP4VCShift Q 3 ) =/= ( NTP4VCShift P 0 ) $.
  sep-a12-a5 $e |- ( NTP4VCShift Q 3 ) =/= ( NTP4VCShift S 0 ) $.
  sep-a12-a7 $e |- ( NTP4VCShift Q 3 ) =/= ( NTP4VCShift P 1 ) $.
  sep-a12-a8 $e |- ( NTP4VCShift Q 3 ) =/= ( NTP4VCShift S 1 ) $.
  sep-a12-a10 $e |- ( NTP4VCShift Q 3 ) =/= ( NTP4VCShift P 2 ) $.
  sep-a12-a11 $e |- ( NTP4VCShift Q 3 ) =/= ( NTP4VCShift S 2 ) $.
  sep-a13-a4 $e |- ( NTP4VCShift P 3 ) =/= ( NTP4VCShift Q 0 ) $.
  sep-a13-a5 $e |- ( NTP4VCShift P 3 ) =/= ( NTP4VCShift S 0 ) $.
  sep-a13-a6 $e |- ( NTP4VCShift P 3 ) =/= ( NTP4VCShift Q 1 ) $.
  sep-a13-a8 $e |- ( NTP4VCShift P 3 ) =/= ( NTP4VCShift S 1 ) $.
  sep-a13-a9 $e |- ( NTP4VCShift P 3 ) =/= ( NTP4VCShift Q 2 ) $.
  sep-a13-a11 $e |- ( NTP4VCShift P 3 ) =/= ( NTP4VCShift S 2 ) $.
  sep-a13-a12 $e |- ( NTP4VCShift P 3 ) =/= ( NTP4VCShift Q 3 ) $.
  sep-a14-a4 $e |- ( NTP4VCShift S 3 ) =/= ( NTP4VCShift Q 0 ) $.
  sep-a14-a3 $e |- ( NTP4VCShift S 3 ) =/= ( NTP4VCShift P 0 ) $.
  sep-a14-a6 $e |- ( NTP4VCShift S 3 ) =/= ( NTP4VCShift Q 1 ) $.
  sep-a14-a7 $e |- ( NTP4VCShift S 3 ) =/= ( NTP4VCShift P 1 ) $.
  sep-a14-a9 $e |- ( NTP4VCShift S 3 ) =/= ( NTP4VCShift Q 2 ) $.
  sep-a14-a10 $e |- ( NTP4VCShift S 3 ) =/= ( NTP4VCShift P 2 ) $.
  sep-a14-a12 $e |- ( NTP4VCShift S 3 ) =/= ( NTP4VCShift Q 3 ) $.
  sep-a14-a13 $e |- ( NTP4VCShift S 3 ) =/= ( NTP4VCShift P 3 ) $.

  region-right $e |- ( G ` ( NTP4VCBase Q ) ) <_ 0 $.
  region-output $e |- ( G ` ( NTP4VCBase P ) ) <_ 0 $.
  region-left $e |- ( G ` ( NTP4VCBase S ) ) <_ 0 $.
  linked-allocation $e |- T e. L $.

  output-positive-base $e |- 0 < ( NTP4VCBase P ) $.
  output-nonnegative-offset $e |- 0 <_ ( NTP4VCOffset P ) $.
  output-valid-end $e |- ( ( NTP4VCOffset P ) + 4 )
    <_ ( T ` ( NTP4VCBase P ) ) $.

  right-nonzero-base $e |- ( NTP4VCBase Q ) =/= 0 $.
  right-nonnegative-offset $e |- 0 <_ ( NTP4VCOffset Q ) $.
  right-valid-end $e |- ( ( NTP4VCOffset Q ) + 4 )
    <_ ( T ` ( NTP4VCBase Q ) ) $.

  left-nonzero-base $e |- ( NTP4VCBase S ) =/= 0 $.
  left-nonnegative-offset $e |- 0 <_ ( NTP4VCOffset S ) $.
  left-valid-end $e |- ( ( NTP4VCOffset S ) + 4 )
    <_ ( T ` ( NTP4VCBase S ) ) $.

  ntp4vc-float-quat-comp-post-goal0 $a |- (
    (
      NTP4VCRead ( NTP4VCM3 F P Q S ) P 0
      =
      (
        (
          (
            (
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 0 )
              x.
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 0 )
            )
            -
            (
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 1 )
              x.
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 1 )
            )
          )
          -
          (
            ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 2 )
            x.
            ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 2 )
          )
        )
        -
        (
          ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 3 )
          x.
          ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 3 )
        )
      )
    )
    /\
    (
      (
        NTP4VCRead ( NTP4VCM3 F P Q S ) P 1
        =
        (
          (
            (
              (
                ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 0 )
                x.
                ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 1 )
              )
              +
              (
                ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 1 )
                x.
                ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 0 )
              )
            )
            +
            (
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 2 )
              x.
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 3 )
            )
          )
          -
          (
            ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 3 )
            x.
            ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 2 )
          )
        )
      )
      /\
      (
        (
          NTP4VCRead ( NTP4VCM3 F P Q S ) P 2
          =
          (
            (
              (
                (
                  ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 0 )
                  x.
                  ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 2 )
                )
                -
                (
                  ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 1 )
                  x.
                  ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 3 )
                )
              )
              +
              (
                ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 2 )
                x.
                ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 0 )
              )
            )
            +
            (
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 3 )
              x.
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 1 )
            )
          )
        )
        /\
        (
          NTP4VCRead ( NTP4VCM3 F P Q S ) P 3
          =
          (
            (
              (
                (
                  ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 0 )
                  x.
                  ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 3 )
                )
                +
                (
                  ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 1 )
                  x.
                  ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 2 )
                )
              )
              -
              (
                ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 2 )
                x.
                ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 1 )
              )
            )
            +
            (
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) S 3 )
              x.
              ( NTP4VCRead ( NTP4VCM3 F P Q S ) Q 0 )
            )
          )
        )
      )
    )
  ) $.
$}
