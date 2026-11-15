$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_call_sqrtf_pre_arg_positive_3_goal6:
  under the generated memory-safety, rotation-matrix, determinant, ordering,
  and branch side conditions, the real expression used as the third square
  root argument is nonnegative. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ. NTP4VCShift changes only the
  integer offset, and NTP4VCRead reads the arbitrary real-valued memory after
  such a shift. The source's nested shift by zero has been normalized.

  The source rotation-matrix record predicate is expanded into its nine real
  matrix-times-transpose component equations, and special orthogonality is
  expanded into the determinant-equals-one equation. The positive-length
  valid_rw and valid_rd predicates and the positive-length separation
  predicate are expanded in the essential hypotheses. The arbitrary source
  region and linked symbols are represented by U and membership in the
  arbitrary predicate extension V.

  In the imported source theory is_float32 is definitionally True, and
  is_finite32 holds for every real; removing those hypotheses is therefore a
  bidirectional logical equivalence. Splitting the source conjunction of
  rotation equations into separate essential hypotheses is likewise
  equivalent. The final declaration is Metamath's native unproved $a
  statement encoding; this file contains no $p proof declaration.
$)

$c NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCRead $.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-read-class $a class ( NTP4VCRead A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-read-def $a |- ( NTP4VCRead A B C ) =
  ( A ` ( NTP4VCShift B C ) ) $.

${
  $d A B C T U V $.

  ntp4vc-input-address $e |- A e. NTP4VCAddr $.
  ntp4vc-output-address $e |- C e. NTP4VCAddr $.
  ntp4vc-input-memory $e |- B e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- U e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- V C_ ( ZZ ^m ZZ ) $.

  ntp4vc-input-region $e |- ( U ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-output-region $e |- ( U ` ( NTP4VCBase C ) ) <_ 0 $.

  ntp4vc-a22-less-than-a11 $e |- (
    ( NTP4VCRead B A 8 ) < ( NTP4VCRead B A 4 )
  ) $.

  ntp4vc-trace-nonpositive $e |- (
    (
      (
        ( NTP4VCRead B A 0 )
        +
        ( NTP4VCRead B A 4 )
      )
      +
      ( NTP4VCRead B A 8 )
    )
    <_ 0
  ) $.

  ntp4vc-linked $e |- T e. V $.

  ntp4vc-output-positive-base $e |- 0 < ( NTP4VCBase C ) $.
  ntp4vc-output-nonnegative-offset $e |- 0 <_ ( NTP4VCOffset C ) $.
  ntp4vc-output-valid-end $e |- (
    ( ( NTP4VCOffset C ) + 4 ) <_ ( T ` ( NTP4VCBase C ) )
  ) $.

  ntp4vc-input-nonzero-base $e |- ( NTP4VCBase A ) =/= 0 $.
  ntp4vc-input-nonnegative-offset $e |- 0 <_ ( NTP4VCOffset A ) $.
  ntp4vc-input-valid-end $e |- (
    ( ( NTP4VCOffset A ) + 9 ) <_ ( T ` ( NTP4VCBase A ) )
  ) $.

  ntp4vc-separated $e |- (
    (
      ( NTP4VCBase A ) =/= ( NTP4VCBase C )
      \/
      ( ( NTP4VCOffset C ) + 4 ) <_ ( NTP4VCOffset A )
    )
    \/
    ( ( NTP4VCOffset A ) + 9 ) <_ ( NTP4VCOffset C )
  ) $.

  ntp4vc-rotation-00 $e |- (
    (
      (
        ( ( NTP4VCRead B A 0 ) x. ( NTP4VCRead B A 0 ) )
        +
        ( ( NTP4VCRead B A 1 ) x. ( NTP4VCRead B A 1 ) )
      )
      +
      ( ( NTP4VCRead B A 2 ) x. ( NTP4VCRead B A 2 ) )
    )
    = 1
  ) $.

  ntp4vc-rotation-01 $e |- (
    (
      (
        ( ( NTP4VCRead B A 0 ) x. ( NTP4VCRead B A 3 ) )
        +
        ( ( NTP4VCRead B A 1 ) x. ( NTP4VCRead B A 4 ) )
      )
      +
      ( ( NTP4VCRead B A 2 ) x. ( NTP4VCRead B A 5 ) )
    )
    = 0
  ) $.

  ntp4vc-rotation-02 $e |- (
    (
      (
        ( ( NTP4VCRead B A 0 ) x. ( NTP4VCRead B A 6 ) )
        +
        ( ( NTP4VCRead B A 1 ) x. ( NTP4VCRead B A 7 ) )
      )
      +
      ( ( NTP4VCRead B A 2 ) x. ( NTP4VCRead B A 8 ) )
    )
    = 0
  ) $.

  ntp4vc-rotation-10 $e |- (
    (
      (
        ( ( NTP4VCRead B A 3 ) x. ( NTP4VCRead B A 0 ) )
        +
        ( ( NTP4VCRead B A 4 ) x. ( NTP4VCRead B A 1 ) )
      )
      +
      ( ( NTP4VCRead B A 5 ) x. ( NTP4VCRead B A 2 ) )
    )
    = 0
  ) $.

  ntp4vc-rotation-11 $e |- (
    (
      (
        ( ( NTP4VCRead B A 3 ) x. ( NTP4VCRead B A 3 ) )
        +
        ( ( NTP4VCRead B A 4 ) x. ( NTP4VCRead B A 4 ) )
      )
      +
      ( ( NTP4VCRead B A 5 ) x. ( NTP4VCRead B A 5 ) )
    )
    = 1
  ) $.

  ntp4vc-rotation-12 $e |- (
    (
      (
        ( ( NTP4VCRead B A 3 ) x. ( NTP4VCRead B A 6 ) )
        +
        ( ( NTP4VCRead B A 4 ) x. ( NTP4VCRead B A 7 ) )
      )
      +
      ( ( NTP4VCRead B A 5 ) x. ( NTP4VCRead B A 8 ) )
    )
    = 0
  ) $.

  ntp4vc-rotation-20 $e |- (
    (
      (
        ( ( NTP4VCRead B A 6 ) x. ( NTP4VCRead B A 0 ) )
        +
        ( ( NTP4VCRead B A 7 ) x. ( NTP4VCRead B A 1 ) )
      )
      +
      ( ( NTP4VCRead B A 8 ) x. ( NTP4VCRead B A 2 ) )
    )
    = 0
  ) $.

  ntp4vc-rotation-21 $e |- (
    (
      (
        ( ( NTP4VCRead B A 6 ) x. ( NTP4VCRead B A 3 ) )
        +
        ( ( NTP4VCRead B A 7 ) x. ( NTP4VCRead B A 4 ) )
      )
      +
      ( ( NTP4VCRead B A 8 ) x. ( NTP4VCRead B A 5 ) )
    )
    = 0
  ) $.

  ntp4vc-rotation-22 $e |- (
    (
      (
        ( ( NTP4VCRead B A 6 ) x. ( NTP4VCRead B A 6 ) )
        +
        ( ( NTP4VCRead B A 7 ) x. ( NTP4VCRead B A 7 ) )
      )
      +
      ( ( NTP4VCRead B A 8 ) x. ( NTP4VCRead B A 8 ) )
    )
    = 1
  ) $.

  ntp4vc-special-orthogonal $e |- (
    (
      (
        (
          (
            ( ( NTP4VCRead B A 0 ) x. ( NTP4VCRead B A 4 ) )
            x.
            ( NTP4VCRead B A 8 )
          )
          +
          (
            ( ( NTP4VCRead B A 1 ) x. ( NTP4VCRead B A 5 ) )
            x.
            ( NTP4VCRead B A 6 )
          )
        )
        +
        (
          ( ( NTP4VCRead B A 2 ) x. ( NTP4VCRead B A 3 ) )
          x.
          ( NTP4VCRead B A 7 )
        )
      )
      -
      (
        (
          (
            ( ( NTP4VCRead B A 0 ) x. ( NTP4VCRead B A 5 ) )
            x.
            ( NTP4VCRead B A 7 )
          )
          +
          (
            ( ( NTP4VCRead B A 1 ) x. ( NTP4VCRead B A 3 ) )
            x.
            ( NTP4VCRead B A 8 )
          )
        )
        +
        (
          ( ( NTP4VCRead B A 2 ) x. ( NTP4VCRead B A 4 ) )
          x.
          ( NTP4VCRead B A 6 )
        )
      )
    )
    = 1
  ) $.

  ntp4vc-branch-order $e |- (
    ( NTP4VCRead B A 0 ) <_ ( NTP4VCRead B A 4 )
    \/
    ( NTP4VCRead B A 0 ) <_ ( NTP4VCRead B A 8 )
  ) $.

  ntp4vc-float-quat-of-rmat-call-sqrtf-pre-arg-positive-3-goal6
    $a |- (
      0 <_
      (
        (
          (
            ( NTP4VCRead B A 4 )
            -
            ( NTP4VCRead B A 0 )
          )
          -
          ( NTP4VCRead B A 8 )
        )
        +
        1
      )
    ) $.
$}
