$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_stdio/__fflush_Why3_ide_VC__fflush_call_write_pre_goal31:
  the fflush write-call verification condition concludes that the stream
  offset field is nonnegative under the generated integer-range, address,
  framing, linking, memory-validity, and private-file-validity assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCFramed, NTP4VCUint32, and NTP4VCSint32 expand the corresponding
  source definitions.

  The source addr_le and addr_lt predicates are represented by arbitrary
  binary relations P and Q on addresses. The two displayed law hypotheses
  preserve their imported axioms exactly: when two addresses have equal
  bases, membership in P or Q is respectively equivalent to comparison of
  their offsets; behavior at unequal bases remains arbitrary.

  NTP4VCValidFile, NTP4VCValidIOFileNoRec, and NTP4VCValidIOFile expand
  p_valid_file, p_valid_io_file_pvt_norec, and p_valid_io_file_pvt without
  dropping any conjunct. Reassociation of conjunctions is bidirectionally
  equivalent to the source nesting, and every source let-bound value is
  expanded at its use.

  The arbitrary integer-valued map G represents region. Membership of the
  allocation map T in the arbitrary set L represents linked, so neither
  imported symbol receives extra laws. All integers range over the full set
  ZZ, and all address and function domains are retained. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCAddrLe NTP4VCAddrLt
  NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCUint32 NTP4VCSint32
  NTP4VCValidFile NTP4VCValidIOFileNoRec NTP4VCValidIOFile
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-addr-le-syntax
  $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax
  $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax
  $a wff ( NTP4VCFramed A B ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-valid-file-syntax
  $a wff ( NTP4VCValidFile A B C ) $.
ntp4vc-valid-io-file-norec-syntax
  $a wff ( NTP4VCValidIOFileNoRec A B C D P Q ) $.
ntp4vc-valid-io-file-syntax
  $a wff ( NTP4VCValidIOFile A B C D P Q ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
  <. B , C >. e. A
) $.

ntp4vc-addr-lt-def $a |- ( ( NTP4VCAddrLt A B C ) <->
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

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-valid-file-def $a |- ( ( NTP4VCValidFile A B C ) <->
  (
    0 <_ ( B ` ( NTP4VCShift C 0 ) )
    /\
    ( NTP4VCValidRW A C 3 )
  )
) $.

ntp4vc-valid-io-file-norec-def $a |- (
  ( NTP4VCValidIOFileNoRec A B C D P Q )
  <->
  (
    (
      (
        ( C ` ( NTP4VCShift D 9 ) )
        =
        ; ; ; ; 1 6 3 8 4
      )
      /\
      (
        (
          0 <_ ( C ` ( NTP4VCShift D 7 ) )
          /\
          ( C ` ( NTP4VCShift D 7 ) )
            < ( C ` ( NTP4VCShift D 9 ) )
        )
        /\
        (
          0 <_ ( C ` ( NTP4VCShift D 8 ) )
          /\
          ( C ` ( NTP4VCShift D 8 ) )
            < ( C ` ( NTP4VCShift D 9 ) )
        )
      )
    )
    /\
    (
      (
        ( NTP4VCValidRW A D ; 1 1 )
        /\
        (
          NTP4VCAddrLe
            P
            ( B ` ( NTP4VCShift D 5 ) )
            ( B ` ( NTP4VCShift D 6 ) )
        )
      )
      /\
      (
        ( NTP4VCValidFile A C ( NTP4VCShift D 0 ) )
        /\
        (
          (
            ( NTP4VCValidRW A ( B ` ( NTP4VCShift D 4 ) ) ; 1 1 )
            /\
            ( NTP4VCValidRW A ( B ` ( NTP4VCShift D 3 ) ) ; 1 1 )
          )
          /\
          (
            (
              NTP4VCSeparated
                D ; 1 1
                ( B ` ( NTP4VCShift D 4 ) ) ; 1 1
            )
            /\
            (
              (
                NTP4VCSeparated
                  D ; 1 1
                  ( B ` ( NTP4VCShift D 3 ) ) ; 1 1
              )
              /\
              (
                NTP4VCSeparated
                  ( B ` ( NTP4VCShift D 4 ) ) ; 1 1
                  ( B ` ( NTP4VCShift D 3 ) ) ; 1 1
              )
            )
          )
        )
      )
      /\
      (
        (
          NTP4VCValidRW
            A
            ( NTP4VCShift ( B ` ( NTP4VCShift D 5 ) ) 0 )
            ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
        )
        /\
        (
          NTP4VCSeparated
            D ; 1 1
            ( NTP4VCShift ( B ` ( NTP4VCShift D 5 ) ) 0 )
            ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
        )
      )
      /\
      (
        (
          NTP4VCSeparated
            ( B ` ( NTP4VCShift D 4 ) ) ; 1 1
            ( NTP4VCShift ( B ` ( NTP4VCShift D 5 ) ) 0 )
            ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
        )
        /\
        (
          (
            NTP4VCSeparated
              ( B ` ( NTP4VCShift D 3 ) ) ; 1 1
              ( NTP4VCShift ( B ` ( NTP4VCShift D 5 ) ) 0 )
              ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
          )
          /\
          (
            NTP4VCAddrLt
              Q
              ( B ` ( NTP4VCShift D 6 ) )
              (
                NTP4VCShift
                  ( B ` ( NTP4VCShift D 5 ) )
                  ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
              )
          )
        )
      )
    )
  )
) $.

ntp4vc-valid-io-file-def $a |- (
  ( NTP4VCValidIOFile A B C D P Q )
  <->
  (
    (
      (
        ( C ` ( NTP4VCShift D 9 ) )
        =
        ; ; ; ; 1 6 3 8 4
      )
      /\
      (
        NTP4VCBase ( B ` ( NTP4VCShift D 6 ) )
      )
      =
      (
        NTP4VCBase ( B ` ( NTP4VCShift D 5 ) )
      )
    )
    /\
    (
      (
        ( B ` ( NTP4VCShift ( B ` ( NTP4VCShift D 3 ) ) 4 ) )
        =
        D
      )
      /\
      (
        ( B ` ( NTP4VCShift ( B ` ( NTP4VCShift D 4 ) ) 3 ) )
        =
        D
      )
    )
    /\
    (
      (
        0 <_ ( C ` ( NTP4VCShift D 7 ) )
        /\
        ( C ` ( NTP4VCShift D 7 ) )
          < ( C ` ( NTP4VCShift D 9 ) )
      )
      /\
      (
        0 <_ ( C ` ( NTP4VCShift D 8 ) )
        /\
        ( C ` ( NTP4VCShift D 8 ) )
          < ( C ` ( NTP4VCShift D 9 ) )
      )
    )
    /\
    (
      (
        ( NTP4VCValidRW A D ; 1 1 )
        /\
        (
          NTP4VCAddrLe
            P
            ( B ` ( NTP4VCShift D 5 ) )
            ( B ` ( NTP4VCShift D 6 ) )
        )
      )
      /\
      (
        ( NTP4VCValidFile A C ( NTP4VCShift D 0 ) )
        /\
        (
          (
            NTP4VCSeparated
              D ; 1 1
              ( B ` ( NTP4VCShift D 4 ) ) ; 1 1
          )
          /\
          (
            NTP4VCSeparated
              D ; 1 1
              ( B ` ( NTP4VCShift D 3 ) ) ; 1 1
          )
          /\
          (
            NTP4VCSeparated
              ( B ` ( NTP4VCShift D 4 ) ) ; 1 1
              ( B ` ( NTP4VCShift D 3 ) ) ; 1 1
          )
        )
      )
    )
    /\
    (
      (
        (
          NTP4VCValidIOFileNoRec
            A B C
            ( B ` ( NTP4VCShift D 4 ) )
            P Q
        )
        /\
        (
          NTP4VCValidIOFileNoRec
            A B C
            ( B ` ( NTP4VCShift D 3 ) )
            P Q
        )
      )
      /\
      (
        NTP4VCValidRW
          A
          ( NTP4VCShift ( B ` ( NTP4VCShift D 5 ) ) 0 )
          ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
      )
    )
    /\
    (
      (
        NTP4VCSeparated
          D ; 1 1
          ( NTP4VCShift ( B ` ( NTP4VCShift D 5 ) ) 0 )
          ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
      )
      /\
      (
        NTP4VCSeparated
          ( B ` ( NTP4VCShift D 4 ) ) ; 1 1
          ( NTP4VCShift ( B ` ( NTP4VCShift D 5 ) ) 0 )
          ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
      )
      /\
      (
        NTP4VCSeparated
          ( B ` ( NTP4VCShift D 3 ) ) ; 1 1
          ( NTP4VCShift ( B ` ( NTP4VCShift D 5 ) ) 0 )
          ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
      )
      /\
      (
        NTP4VCAddrLt
          Q
          ( B ` ( NTP4VCShift D 6 ) )
          (
            NTP4VCShift
              ( B ` ( NTP4VCShift D 5 ) )
              ( ; 3 2 + ( C ` ( NTP4VCShift D 9 ) ) )
          )
      )
    )
  )
) $.

${
  $d x y A B C D E F G L P Q T $.

  $( Source parameters:
     A=a_1, B=a, C=t_2, D=t_1, E=i, F=i_1, T=t,
     G=region, L=linked extension, P=addr_le relation,
     Q=addr_lt relation. Source let bindings are expanded at use. $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-pointer-map $e |- C e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-int-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-addr-le-relation $e |- P C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- Q C_ ( NTP4VCAddr X. NTP4VCAddr ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe P x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-addr-lt-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLt Q x y )
        <->
        ( NTP4VCOffset x ) < ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-i-nonzero $e |- E =/= 0 $.

  ntp4vc-offset-field-zero $e |- (
    D ` ( NTP4VCShift A 7 )
  ) = 0 $.

  ntp4vc-base-a2-a $e |- (
    NTP4VCBase ( C ` ( NTP4VCShift A 5 ) )
  ) = ( NTP4VCBase B ) $.

  ntp4vc-base-next-a $e |- (
    NTP4VCBase ( C ` ( NTP4VCShift A 6 ) )
  ) = ( NTP4VCBase B ) $.

  ntp4vc-base-next-a2 $e |- (
    NTP4VCBase ( C ` ( NTP4VCShift A 6 ) )
  ) = (
    NTP4VCBase ( C ` ( NTP4VCShift A 5 ) )
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ E $.
  ntp4vc-i1-le-i $e |- F <_ E $.
  ntp4vc-region-a1 $e |- ( G ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-i1-lower-bound $e |- -u 1 <_ F $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed G C ) $.
  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 F ) $.

  ntp4vc-capacity-uint32 $e |- (
    NTP4VCUint32 ( D ` ( NTP4VCShift A 9 ) )
  ) $.

  ntp4vc-position-uint32 $e |- (
    NTP4VCUint32 ( D ` ( NTP4VCShift A 8 ) )
  ) $.

  ntp4vc-valid-io-file $e |- (
    NTP4VCValidIOFile T C D A P Q
  ) $.

  ntp4vc-a2-le-a $e |- (
    NTP4VCAddrLe
      P
      ( C ` ( NTP4VCShift A 5 ) )
      B
  ) $.

  ntp4vc-write-buffer-valid $e |- (
    NTP4VCValidRW T ( NTP4VCShift B 0 ) E
  ) $.

  ntp4vc-offset-sint32 $e |- (
    NTP4VCSint32
      ( D ` ( NTP4VCShift ( NTP4VCShift A 0 ) 0 ) )
  ) $.

  ntp4vc-a-le-buffer-end $e |- (
    NTP4VCAddrLe
      P
      B
      (
        NTP4VCShift
          ( C ` ( NTP4VCShift A 5 ) )
          ( ; 3 2 + ( D ` ( NTP4VCShift A 9 ) ) )
      )
  ) $.

  ntp4vc-fflush-call-write-pre-goal31 $a |- 0 <_
    ( D ` ( NTP4VCShift ( NTP4VCShift A 0 ) 0 ) ) $.
$}
