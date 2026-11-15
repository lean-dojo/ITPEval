$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_a00_max_post_goal9:
  under the generated memory-safety, rotation-matrix, branch, and
  floating-point side conditions, the a00-max conversion from a real rotation
  matrix writes the corresponding four real quaternion components. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ. NTP4VCShift changes only the
  integer offset, NTP4VCRead reads a real-valued memory after a shift, and
  NTP4VCUpdate is the source functional update on the full address domain.
  Nested zero shifts from the source let-expressions have been normalized by
  integer addition.

  NTP4VCRotation expands the source matrix-times-transpose equality into its
  nine real component equations. NTP4VCSpecialOrthogonal expands its
  determinant-equals-one predicate. The four NTP4VCM families are exactly the
  four sequences of functional updates in the source control-flow branches,
  and NTP4VCPost is the proposition-valued conditional expanded as
  (condition -> then-branch) /\ (-. condition -> else-branch).

  In the imported source theory is_float32 is definitionally True, while
  is_finite32 is asserted for every real. Those hypotheses therefore disappear
  by bidirectional logical equivalence. The positive-length valid_rw and
  valid_rd predicates and the separation predicate are expanded in the final
  context. The arbitrary source region and linked symbols are represented by
  U and membership in the arbitrary predicate extension V.

  The conclusion expands the source quaternion-record equality into the four
  component equations, retaining real division and the real square root.
  The final declaration is Metamath's native unproved $a statement encoding;
  this candidate file contains no local $p proof declaration. Its imported
  set.mm dependency contains the standard library proofs.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCRead
  NTP4VCUpdate
  NTP4VCM00 NTP4VCM01 NTP4VCM02 NTP4VCM03
  NTP4VCM10 NTP4VCM11 NTP4VCM12 NTP4VCM13
  NTP4VCM20 NTP4VCM21 NTP4VCM22 NTP4VCM23
  NTP4VCM30 NTP4VCM31 NTP4VCM32 NTP4VCM33
  NTP4VCRotation NTP4VCSpecialOrthogonal
  NTP4VCCase0 NTP4VCCase1 NTP4VCCase2 NTP4VCCase3 NTP4VCTail NTP4VCPost
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-read-class $a class ( NTP4VCRead A B C ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.

ntp4vc-m00-class $a class ( NTP4VCM00 A B C ) $.
ntp4vc-m01-class $a class ( NTP4VCM01 A B C D E ) $.
ntp4vc-m02-class $a class ( NTP4VCM02 A B C D E ) $.
ntp4vc-m03-class $a class ( NTP4VCM03 A B C D E ) $.

ntp4vc-m10-class $a class ( NTP4VCM10 A B C D ) $.
ntp4vc-m11-class $a class ( NTP4VCM11 A B C D E ) $.
ntp4vc-m12-class $a class ( NTP4VCM12 A B C D E ) $.
ntp4vc-m13-class $a class ( NTP4VCM13 A B C D E ) $.

ntp4vc-m20-class $a class ( NTP4VCM20 A B C D ) $.
ntp4vc-m21-class $a class ( NTP4VCM21 A B C D ) $.
ntp4vc-m22-class $a class ( NTP4VCM22 A B C D E ) $.
ntp4vc-m23-class $a class ( NTP4VCM23 A B C D E ) $.

ntp4vc-m30-class $a class ( NTP4VCM30 A B C D ) $.
ntp4vc-m31-class $a class ( NTP4VCM31 A B C D ) $.
ntp4vc-m32-class $a class ( NTP4VCM32 A B C D ) $.
ntp4vc-m33-class $a class ( NTP4VCM33 A B C D E ) $.

ntp4vc-rotation-syntax $a wff ( NTP4VCRotation A B ) $.
ntp4vc-special-orthogonal-syntax
  $a wff ( NTP4VCSpecialOrthogonal A B ) $.
ntp4vc-case0-syntax $a wff ( NTP4VCCase0 A B C D E F G ) $.
ntp4vc-case1-syntax $a wff ( NTP4VCCase1 A B C D E F G ) $.
ntp4vc-case2-syntax $a wff ( NTP4VCCase2 A B C D E F G ) $.
ntp4vc-case3-syntax $a wff ( NTP4VCCase3 A B C D E F G ) $.
ntp4vc-tail-syntax
  $a wff ( NTP4VCTail A B C D E F G H I J ) $.
ntp4vc-post-syntax
  $a wff
    ( NTP4VCPost A B C D E F G H I J K L M N O P Q R S )
  $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-read-def $a |- ( NTP4VCRead A B C ) =
  ( A ` ( NTP4VCShift B C ) ) $.

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    ( x e. NTP4VCAddr |-> if ( x = B , C , ( A ` x ) ) ) $.
$}

ntp4vc-m00-def $a |- ( NTP4VCM00 A B C ) =
  ( NTP4VCUpdate A ( NTP4VCShift C 0 ) ( ( 1 / 2 ) x. B ) ) $.

ntp4vc-m01-def $a |- ( NTP4VCM01 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM00 A B E )
    ( NTP4VCShift E 1 )
    (
      (
        ( ( NTP4VCM00 A B E ) ` ( NTP4VCShift D 5 ) )
        -
        ( ( NTP4VCM00 A B E ) ` ( NTP4VCShift D 7 ) )
      )
      / C
    )
  ) $.

ntp4vc-m02-def $a |- ( NTP4VCM02 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM01 A B C D E )
    ( NTP4VCShift E 2 )
    (
      (
        ( ( NTP4VCM01 A B C D E ) ` ( NTP4VCShift D 6 ) )
        -
        ( ( NTP4VCM01 A B C D E ) ` ( NTP4VCShift D 2 ) )
      )
      / C
    )
  ) $.

ntp4vc-m03-def $a |- ( NTP4VCM03 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM02 A B C D E )
    ( NTP4VCShift E 3 )
    (
      (
        ( ( NTP4VCM02 A B C D E ) ` ( NTP4VCShift D 1 ) )
        -
        ( ( NTP4VCM02 A B C D E ) ` ( NTP4VCShift D 3 ) )
      )
      / C
    )
  ) $.

ntp4vc-m10-def $a |- ( NTP4VCM10 A B C D ) =
  ( NTP4VCUpdate
    A
    ( NTP4VCShift D 0 )
    (
      (
        ( NTP4VCRead A C 5 )
        -
        ( NTP4VCRead A C 7 )
      )
      / B
    )
  ) $.

ntp4vc-m11-def $a |- ( NTP4VCM11 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM10 A B D E )
    ( NTP4VCShift E 1 )
    ( ( 1 / 2 ) x. C )
  ) $.

ntp4vc-m12-def $a |- ( NTP4VCM12 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM11 A B C D E )
    ( NTP4VCShift E 2 )
    (
      (
        ( ( NTP4VCM11 A B C D E ) ` ( NTP4VCShift D 1 ) )
        +
        ( ( NTP4VCM11 A B C D E ) ` ( NTP4VCShift D 3 ) )
      )
      / B
    )
  ) $.

ntp4vc-m13-def $a |- ( NTP4VCM13 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM12 A B C D E )
    ( NTP4VCShift E 3 )
    (
      (
        ( ( NTP4VCM12 A B C D E ) ` ( NTP4VCShift D 6 ) )
        +
        ( ( NTP4VCM12 A B C D E ) ` ( NTP4VCShift D 2 ) )
      )
      / B
    )
  ) $.

ntp4vc-m20-def $a |- ( NTP4VCM20 A B C D ) =
  ( NTP4VCUpdate
    A
    ( NTP4VCShift D 0 )
    (
      (
        ( NTP4VCRead A C 6 )
        -
        ( NTP4VCRead A C 2 )
      )
      / B
    )
  ) $.

ntp4vc-m21-def $a |- ( NTP4VCM21 A B C D ) =
  ( NTP4VCUpdate
    ( NTP4VCM20 A B C D )
    ( NTP4VCShift D 1 )
    (
      (
        ( ( NTP4VCM20 A B C D ) ` ( NTP4VCShift C 1 ) )
        +
        ( ( NTP4VCM20 A B C D ) ` ( NTP4VCShift C 3 ) )
      )
      / B
    )
  ) $.

ntp4vc-m22-def $a |- ( NTP4VCM22 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM21 A B D E )
    ( NTP4VCShift E 2 )
    ( ( 1 / 2 ) x. C )
  ) $.

ntp4vc-m23-def $a |- ( NTP4VCM23 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM22 A B C D E )
    ( NTP4VCShift E 3 )
    (
      (
        ( ( NTP4VCM22 A B C D E ) ` ( NTP4VCShift D 5 ) )
        +
        ( ( NTP4VCM22 A B C D E ) ` ( NTP4VCShift D 7 ) )
      )
      / B
    )
  ) $.

ntp4vc-m30-def $a |- ( NTP4VCM30 A B C D ) =
  ( NTP4VCUpdate
    A
    ( NTP4VCShift D 0 )
    (
      (
        ( NTP4VCRead A C 1 )
        -
        ( NTP4VCRead A C 3 )
      )
      / B
    )
  ) $.

ntp4vc-m31-def $a |- ( NTP4VCM31 A B C D ) =
  ( NTP4VCUpdate
    ( NTP4VCM30 A B C D )
    ( NTP4VCShift D 1 )
    (
      (
        ( ( NTP4VCM30 A B C D ) ` ( NTP4VCShift C 6 ) )
        +
        ( ( NTP4VCM30 A B C D ) ` ( NTP4VCShift C 2 ) )
      )
      / B
    )
  ) $.

ntp4vc-m32-def $a |- ( NTP4VCM32 A B C D ) =
  ( NTP4VCUpdate
    ( NTP4VCM31 A B C D )
    ( NTP4VCShift D 2 )
    (
      (
        ( ( NTP4VCM31 A B C D ) ` ( NTP4VCShift C 5 ) )
        +
        ( ( NTP4VCM31 A B C D ) ` ( NTP4VCShift C 7 ) )
      )
      / B
    )
  ) $.

ntp4vc-m33-def $a |- ( NTP4VCM33 A B C D E ) =
  ( NTP4VCUpdate
    ( NTP4VCM32 A B D E )
    ( NTP4VCShift E 3 )
    ( ( 1 / 2 ) x. C )
  ) $.

ntp4vc-rotation-def $a |- ( ( NTP4VCRotation A B ) <->
  (
    (
      (
        (
          ( ( NTP4VCRead A B 0 ) x. ( NTP4VCRead A B 0 ) )
          +
          ( ( NTP4VCRead A B 1 ) x. ( NTP4VCRead A B 1 ) )
        )
        +
        ( ( NTP4VCRead A B 2 ) x. ( NTP4VCRead A B 2 ) )
      )
      = 1
    )
    /\
    (
      (
        (
          ( ( NTP4VCRead A B 0 ) x. ( NTP4VCRead A B 3 ) )
          +
          ( ( NTP4VCRead A B 1 ) x. ( NTP4VCRead A B 4 ) )
        )
        +
        ( ( NTP4VCRead A B 2 ) x. ( NTP4VCRead A B 5 ) )
      )
      = 0
      /\
      (
        (
          (
            ( ( NTP4VCRead A B 0 ) x. ( NTP4VCRead A B 6 ) )
            +
            ( ( NTP4VCRead A B 1 ) x. ( NTP4VCRead A B 7 ) )
          )
          +
          ( ( NTP4VCRead A B 2 ) x. ( NTP4VCRead A B 8 ) )
        )
        = 0
        /\
        (
          (
            (
              ( ( NTP4VCRead A B 3 ) x. ( NTP4VCRead A B 0 ) )
              +
              ( ( NTP4VCRead A B 4 ) x. ( NTP4VCRead A B 1 ) )
            )
            +
            ( ( NTP4VCRead A B 5 ) x. ( NTP4VCRead A B 2 ) )
          )
          = 0
          /\
          (
            (
              (
                ( ( NTP4VCRead A B 3 ) x. ( NTP4VCRead A B 3 ) )
                +
                ( ( NTP4VCRead A B 4 ) x. ( NTP4VCRead A B 4 ) )
              )
              +
              ( ( NTP4VCRead A B 5 ) x. ( NTP4VCRead A B 5 ) )
            )
            = 1
            /\
            (
              (
                (
                  ( ( NTP4VCRead A B 3 ) x. ( NTP4VCRead A B 6 ) )
                  +
                  ( ( NTP4VCRead A B 4 ) x. ( NTP4VCRead A B 7 ) )
                )
                +
                ( ( NTP4VCRead A B 5 ) x. ( NTP4VCRead A B 8 ) )
              )
              = 0
              /\
              (
                (
                  (
                    ( ( NTP4VCRead A B 6 ) x. ( NTP4VCRead A B 0 ) )
                    +
                    ( ( NTP4VCRead A B 7 ) x. ( NTP4VCRead A B 1 ) )
                  )
                  +
                  ( ( NTP4VCRead A B 8 ) x. ( NTP4VCRead A B 2 ) )
                )
                = 0
                /\
                (
                  (
                    (
                      ( ( NTP4VCRead A B 6 ) x.
                        ( NTP4VCRead A B 3 ) )
                      +
                      ( ( NTP4VCRead A B 7 ) x.
                        ( NTP4VCRead A B 4 ) )
                    )
                    +
                    ( ( NTP4VCRead A B 8 ) x.
                      ( NTP4VCRead A B 5 ) )
                  )
                  = 0
                  /\
                  (
                    (
                      (
                        ( ( NTP4VCRead A B 6 ) x.
                          ( NTP4VCRead A B 6 ) )
                        +
                        ( ( NTP4VCRead A B 7 ) x.
                          ( NTP4VCRead A B 7 ) )
                      )
                      +
                      ( ( NTP4VCRead A B 8 ) x.
                        ( NTP4VCRead A B 8 ) )
                    )
                    = 1
                  )
                )
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-special-orthogonal-def
  $a |- ( ( NTP4VCSpecialOrthogonal A B ) <->
    (
      (
        (
          (
            (
              ( NTP4VCRead A B 0 ) x.
              ( NTP4VCRead A B 4 )
            )
            x.
            ( NTP4VCRead A B 8 )
          )
          +
          (
            (
              ( NTP4VCRead A B 1 ) x.
              ( NTP4VCRead A B 5 )
            )
            x.
            ( NTP4VCRead A B 6 )
          )
        )
        +
        (
          (
            ( NTP4VCRead A B 2 ) x.
            ( NTP4VCRead A B 3 )
          )
          x.
          ( NTP4VCRead A B 7 )
        )
      )
      -
      (
        (
          (
            (
              ( NTP4VCRead A B 0 ) x.
              ( NTP4VCRead A B 5 )
            )
            x.
            ( NTP4VCRead A B 7 )
          )
          +
          (
            (
              ( NTP4VCRead A B 1 ) x.
              ( NTP4VCRead A B 3 )
            )
            x.
            ( NTP4VCRead A B 8 )
          )
        )
        +
        (
          (
            ( NTP4VCRead A B 2 ) x.
            ( NTP4VCRead A B 4 )
          )
          x.
          ( NTP4VCRead A B 6 )
        )
      )
      = 1
    )
  ) $.

ntp4vc-case0-def $a |- ( ( NTP4VCCase0 A B C D E F G ) <->
  (
    A = E
    /\
    (
      ( 2 x. B ) = C
      /\
      (
        ( NTP4VCM03 A B C F G ) = D
        /\
        (
          0 <_ B
          /\
          (
            0 <_
            (
              1
              +
              (
                (
                  ( NTP4VCRead A F 0 )
                  +
                  ( NTP4VCRead A F 4 )
                )
                +
                ( NTP4VCRead A F 8 )
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-case1-def $a |- ( ( NTP4VCCase1 A B C D E F G ) <->
  (
    B = A
    /\
    (
      ( 2 x. C ) = D
      /\
      (
        ( NTP4VCM13 B D C F G ) = E
        /\
        (
          0 <_ C
          /\
          (
            0 <_
            (
              (
                (
                  ( NTP4VCRead B F 0 )
                  -
                  ( NTP4VCRead B F 4 )
                )
                -
                ( NTP4VCRead B F 8 )
              )
              +
              1
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-case2-def $a |- ( ( NTP4VCCase2 A B C D E F G ) <->
  (
    C = A
    /\
    (
      ( 2 x. B ) = D
      /\
      (
        ( NTP4VCM23 C D B F G ) = E
        /\
        (
          0 <_ B
          /\
          (
            0 <_
            (
              (
                (
                  ( NTP4VCRead C F 4 )
                  -
                  ( NTP4VCRead C F 0 )
                )
                -
                ( NTP4VCRead C F 8 )
              )
              +
              1
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-case3-def $a |- ( ( NTP4VCCase3 A B C D E F G ) <->
  (
    C = A
    /\
    (
      ( 2 x. B ) = D
      /\
      (
        ( NTP4VCM33 C D B F G ) = E
        /\
        (
          0 <_ B
          /\
          (
            0 <_
            (
              (
                (
                  ( NTP4VCRead C F 8 )
                  -
                  ( NTP4VCRead C F 0 )
                )
                -
                ( NTP4VCRead C F 4 )
              )
              +
              1
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-tail-def $a |- ( ( NTP4VCTail A B C D E F G H I J ) <->
  (
    (
      ( NTP4VCRead A I 8 ) < ( NTP4VCRead A I 4 )
      ->
      ( NTP4VCCase2 A B C D H I J )
    )
    /\
    (
      -. ( NTP4VCRead A I 8 ) < ( NTP4VCRead A I 4 )
      ->
      ( NTP4VCCase3 A E F G H I J )
    )
  )
) $.

ntp4vc-post-def
  $a |- (
    ( NTP4VCPost A B C D E F G H I J K L M N O P Q R S )
    <->
    (
      (
        0 <
        (
          (
            ( NTP4VCRead B A 0 )
            +
            ( NTP4VCRead B A 4 )
          )
          +
          ( NTP4VCRead B A 8 )
        )
        ->
        ( NTP4VCCase0 D E F Q B A C )
      )
      /\
      (
        -.
        0 <
        (
          (
            ( NTP4VCRead B A 0 )
            +
            ( NTP4VCRead B A 4 )
          )
          +
          ( NTP4VCRead B A 8 )
        )
        ->
        (
          R = B
          /\
          (
            (
              ( NTP4VCRead R A 4 ) < ( NTP4VCRead R A 0 )
              ->
              (
                S = R
                /\
                (
                  (
                    ( NTP4VCRead S A 8 ) < ( NTP4VCRead S A 0 )
                    ->
                    ( NTP4VCCase1 S G I H Q A C )
                  )
                  /\
                  (
                    -. ( NTP4VCRead S A 8 ) < ( NTP4VCRead S A 0 )
                    ->
                    (
                      J = S
                      /\
                      ( NTP4VCTail J K L M N O P Q A C )
                    )
                  )
                )
              )
            )
            /\
            (
              -. ( NTP4VCRead R A 4 ) < ( NTP4VCRead R A 0 )
              ->
              (
                J = R
                /\
                ( NTP4VCTail J K L M N O P Q A C )
              )
            )
          )
        )
      )
    )
  ) $.

${
  $d A B C D E F G H I J K L M N O P Q R S T U V $.

  ntp4vc-input-address $e |- A e. NTP4VCAddr $.
  ntp4vc-output-address $e |- C e. NTP4VCAddr $.

  ntp4vc-input-memory $e |- B e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-branch0-memory $e |- D e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-branch1-memory $e |- G e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-test-memory $e |- J e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-branch2-memory $e |- L e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-branch3-memory $e |- O e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-output-memory $e |- Q e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-copy-memory $e |- R e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-second-test-memory $e |- S e. ( RR ^m NTP4VCAddr ) $.

  ntp4vc-r3-real $e |- E e. RR $.
  ntp4vc-r7-real $e |- F e. RR $.
  ntp4vc-r6-real $e |- H e. RR $.
  ntp4vc-r2-real $e |- I e. RR $.
  ntp4vc-r1-real $e |- K e. RR $.
  ntp4vc-r5-real $e |- M e. RR $.
  ntp4vc-r-real $e |- N e. RR $.
  ntp4vc-r4-real $e |- P e. RR $.

  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- U e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- V C_ ( ZZ ^m ZZ ) $.

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

  ntp4vc-input-region $e |- ( U ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-output-region $e |- ( U ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-a11-below-a00 $e |- (
    ( NTP4VCRead B A 4 ) < ( NTP4VCRead B A 0 )
  ) $.
  ntp4vc-a22-below-a00 $e |- (
    ( NTP4VCRead B A 8 ) < ( NTP4VCRead B A 0 )
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

  ntp4vc-rotation $e |- ( NTP4VCRotation B A ) $.
  ntp4vc-special-orthogonal $e |- ( NTP4VCSpecialOrthogonal B A ) $.
  ntp4vc-postcondition $e |- (
    NTP4VCPost A B C D E F G H I J K L M N O P Q R S
  ) $.
  ntp4vc-r2-sqrt $e |- I = (
    sqrt
    `
    (
      (
        (
          ( NTP4VCRead G A 0 )
          -
          ( NTP4VCRead G A 4 )
        )
        -
        ( NTP4VCRead G A 8 )
      )
      +
      1
    )
  ) $.

  ntp4vc-float-quat-of-rmat-a00-max-post-goal9 $a |- (
    (
      ( NTP4VCRead Q C 0 )
      =
      (
        (
          ( NTP4VCRead Q A 5 )
          -
          ( NTP4VCRead Q A 7 )
        )
        /
        (
          2
          x.
          (
            sqrt
            `
            (
              (
                (
                  1
                  +
                  ( NTP4VCRead Q A 0 )
                )
                -
                ( NTP4VCRead Q A 4 )
              )
              -
              ( NTP4VCRead Q A 8 )
            )
          )
        )
      )
    )
    /\
    (
      (
        ( NTP4VCRead Q C 1 )
        =
        (
          ( 1 / 2 )
          x.
          (
            sqrt
            `
            (
              (
                (
                  1
                  +
                  ( NTP4VCRead Q A 0 )
                )
                -
                ( NTP4VCRead Q A 4 )
              )
              -
              ( NTP4VCRead Q A 8 )
            )
          )
        )
      )
      /\
      (
        (
          ( NTP4VCRead Q C 2 )
          =
          (
            (
              ( NTP4VCRead Q A 3 )
              +
              ( NTP4VCRead Q A 1 )
            )
            /
            (
              2
              x.
              (
                sqrt
                `
                (
                  (
                    (
                      1
                      +
                      ( NTP4VCRead Q A 0 )
                    )
                    -
                    ( NTP4VCRead Q A 4 )
                  )
                  -
                  ( NTP4VCRead Q A 8 )
                )
              )
            )
          )
        )
        /\
        (
          ( NTP4VCRead Q C 3 )
          =
          (
            (
              ( NTP4VCRead Q A 6 )
              +
              ( NTP4VCRead Q A 2 )
            )
            /
            (
              2
              x.
              (
                sqrt
                `
                (
                  (
                    (
                      1
                      +
                      ( NTP4VCRead Q A 0 )
                    )
                    -
                    ( NTP4VCRead Q A 4 )
                  )
                  -
                  ( NTP4VCRead Q A 8 )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}
