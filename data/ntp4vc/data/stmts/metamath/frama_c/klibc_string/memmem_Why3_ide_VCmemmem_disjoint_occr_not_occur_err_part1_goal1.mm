$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/memmem_Why3_ide_VCmemmem_disjoint_occr_not_occur_err_part1_goal1:
  the memmem verification condition concludes a disjunction of zero-length
  and length-order cases or the existence of a nonnegative offset whose
  shifted memory values agree throughout the requested integer interval,
  under the generated region, linking, unsigned-length, memory-validity, and
  buffer-separation assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated, and
  NTP4VCUint32 directly expand the corresponding source definitions.

  The arbitrary integer-valued map R represents the source region function,
  and membership of the allocation map E in the arbitrary set L represents
  the source linked predicate. Thus the source-uninterpreted symbols retain
  their full domains without being assigned extra laws. Source let-bindings
  a_4 = shift a_2 0 and a_5 = shift a_3 0 are expanded at their uses. The
  existential offset and the inner universal index both retain the full
  integer domain. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCValidRW NTP4VCSeparated NTP4VCUint32
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
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

${
  $d x y A B C D E F G H L R $.

  $( Source parameters:
     A=a_2, B=a_3, C=i, D=i_1, E=t, F=t_1, G=a_1, H=a.
     R is region and L is the extension of linked. Source lets are expanded
     as a_4=shift(A,0) and a_5=shift(B,0). $)

  ntp4vc-a2-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-value-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- G e. NTP4VCAddr $.
  ntp4vc-a-address $e |- H e. NTP4VCAddr $.

  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ C $.
  ntp4vc-i1-nonnegative $e |- 0 <_ D $.
  ntp4vc-region-a2 $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( R ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- E e. L $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 D ) $.

  ntp4vc-a2-valid-rw $e |- (
    NTP4VCValidRW E ( NTP4VCShift A 0 ) D
  ) $.

  ntp4vc-a3-valid-rw $e |- (
    NTP4VCValidRW E ( NTP4VCShift B 0 ) C
  ) $.

  ntp4vc-buffers-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCShift B 0 ) C
      ( NTP4VCShift A 0 ) D
  ) $.

  ntp4vc-memmem-disjoint-occr-not-occur-err-part1-goal1 $a |- (
    C = 0
    \/
    (
      D = 0
      \/
      (
        C < D
        \/
        (
          (
            C =/= 0
            /\
            (
              D =/= 0
              /\
              D <_ C
            )
          )
          \/
          E. x e. ZZ
            (
              0 <_ x
              /\
              (
                ( x + D ) <_ C
                /\
                A. y e. ZZ
                  (
                    (
                      F ` ( NTP4VCShift G ( y + x ) )
                    )
                    =
                    (
                      F ` ( NTP4VCShift H y )
                    )
                    \/
                    (
                      y < 0
                      \/
                      D <_ y
                    )
                  )
              )
            )
        )
      )
    )
  ) $.
$}
