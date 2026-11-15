$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_stdio/_fwrite_Why3_ide_VC_fwrite_call___fflush_pre_part4_goal16:
  the fwrite verification condition preserves the private FILE validity
  predicate after three integer-memory updates, under the generated integer
  range, memory, framing, linking, constancy, writable-buffer, and quantified
  buffer-content assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base, offset, and shift
  expanded from the source structure. NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCFramed, NTP4VCUint32, NTP4VCValidFile,
  NTP4VCValidIOFileNoRec, and NTP4VCValidIOFile directly render the
  corresponding source definitions. In particular, both private FILE
  predicates retain every memory-validity, ordering, pointer-link, range, and
  separation conjunct.

  The arbitrary relations U and V represent addr_le and addr_lt. Their source
  axioms, which identify them with offset order only when bases agree, are
  explicit hypotheses; no stronger total address order is assumed. The
  arbitrary map R and sets L and S represent region, linked, and sconst.
  NTP4VCUpdate is full-domain functional update, and the three nested updates
  have the same order as Function.update, fun_updt, and Isabelle map update in
  the joint ground truths.

  The source occurrence to_uint32 (i_4 - 1) is displayed as i_4 - 1. The
  hypotheses that i_4 is uint32 and nonzero imply that i_4 - 1 is uint32, so
  the imported source axiom id_uint32 makes this replacement bidirectionally
  equivalent in this verification condition. The final declaration is
  Metamath's native unproved $a statement encoding; this database adds no $p
  proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCBufferSize NTP4VCHeaderSize NTP4VCFileSize
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCValidRW NTP4VCSeparated
  NTP4VCFramed NTP4VCUint32 NTP4VCUpdate
  NTP4VCValidFile NTP4VCValidIOFileNoRec NTP4VCValidIOFile
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-buffer-size-class $a class NTP4VCBufferSize $.
ntp4vc-header-size-class $a class NTP4VCHeaderSize $.
ntp4vc-file-size-class $a class NTP4VCFileSize $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax $a wff ( NTP4VCFramed A B ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-valid-file-syntax $a wff ( NTP4VCValidFile A B C ) $.
ntp4vc-valid-io-file-norec-syntax
  $a wff ( NTP4VCValidIOFileNoRec A B C D P Q ) $.
ntp4vc-valid-io-file-syntax
  $a wff ( NTP4VCValidIOFile A B C D P Q ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-buffer-size-def $a |- NTP4VCBufferSize =
  ; ; ; ; 1 6 3 8 4 $.
ntp4vc-header-size-def $a |- NTP4VCHeaderSize = ; 3 2 $.
ntp4vc-file-size-def $a |- NTP4VCFileSize = ; 1 1 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
  <. B , C >. e. A ) $.

ntp4vc-addr-lt-def $a |- ( ( NTP4VCAddrLt A B C ) <->
  <. B , C >. e. A ) $.

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

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

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
    ( C ` ( NTP4VCShift D 9 ) ) = NTP4VCBufferSize
    /\
    (
      0 <_ ( C ` ( NTP4VCShift D 7 ) )
      /\
      (
        ( C ` ( NTP4VCShift D 7 ) )
        <
        ( C ` ( NTP4VCShift D 9 ) )
        /\
        (
          0 <_ ( C ` ( NTP4VCShift D 8 ) )
          /\
          (
            ( C ` ( NTP4VCShift D 8 ) )
            <
            ( C ` ( NTP4VCShift D 9 ) )
            /\
            (
              ( NTP4VCValidRW A D NTP4VCFileSize )
              /\
              (
                NTP4VCAddrLe
                  P
                  ( B ` ( NTP4VCShift D 5 ) )
                  ( B ` ( NTP4VCShift D 6 ) )
                /\
                (
                  NTP4VCValidFile A C ( NTP4VCShift D 0 )
                  /\
                  (
                    NTP4VCValidRW
                      A
                      ( B ` ( NTP4VCShift D 4 ) )
                      NTP4VCFileSize
                    /\
                    (
                      NTP4VCValidRW
                        A
                        ( B ` ( NTP4VCShift D 3 ) )
                        NTP4VCFileSize
                      /\
                      (
                        NTP4VCSeparated
                          D NTP4VCFileSize
                          ( B ` ( NTP4VCShift D 4 ) )
                          NTP4VCFileSize
                        /\
                        (
                          NTP4VCSeparated
                            D NTP4VCFileSize
                            ( B ` ( NTP4VCShift D 3 ) )
                            NTP4VCFileSize
                          /\
                          (
                            NTP4VCSeparated
                              ( B ` ( NTP4VCShift D 4 ) )
                              NTP4VCFileSize
                              ( B ` ( NTP4VCShift D 3 ) )
                              NTP4VCFileSize
                            /\
                            (
                              NTP4VCValidRW
                                A
                                (
                                  NTP4VCShift
                                    ( B ` ( NTP4VCShift D 5 ) )
                                    0
                                )
                                (
                                  NTP4VCHeaderSize
                                  +
                                  ( C ` ( NTP4VCShift D 9 ) )
                                )
                              /\
                              (
                                NTP4VCSeparated
                                  D NTP4VCFileSize
                                  (
                                    NTP4VCShift
                                      ( B ` ( NTP4VCShift D 5 ) )
                                      0
                                  )
                                  (
                                    NTP4VCHeaderSize
                                    +
                                    ( C ` ( NTP4VCShift D 9 ) )
                                  )
                                /\
                                (
                                  NTP4VCSeparated
                                    ( B ` ( NTP4VCShift D 4 ) )
                                    NTP4VCFileSize
                                    (
                                      NTP4VCShift
                                        ( B ` ( NTP4VCShift D 5 ) )
                                        0
                                    )
                                    (
                                      NTP4VCHeaderSize
                                      +
                                      ( C ` ( NTP4VCShift D 9 ) )
                                    )
                                  /\
                                  (
                                    NTP4VCSeparated
                                      ( B ` ( NTP4VCShift D 3 ) )
                                      NTP4VCFileSize
                                      (
                                        NTP4VCShift
                                          ( B ` ( NTP4VCShift D 5 ) )
                                          0
                                      )
                                      (
                                        NTP4VCHeaderSize
                                        +
                                        ( C ` ( NTP4VCShift D 9 ) )
                                      )
                                    /\
                                    (
                                      NTP4VCAddrLt
                                        Q
                                        ( B ` ( NTP4VCShift D 6 ) )
                                        (
                                          NTP4VCShift
                                            ( B ` ( NTP4VCShift D 5 ) )
                                            (
                                              NTP4VCHeaderSize
                                              +
                                              ( C ` ( NTP4VCShift D 9 ) )
                                            )
                                        )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
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

ntp4vc-valid-io-file-def $a |- (
  ( NTP4VCValidIOFile A B C D P Q )
  <->
  (
    ( C ` ( NTP4VCShift D 9 ) ) = NTP4VCBufferSize
    /\
    (
      (
        NTP4VCBase ( B ` ( NTP4VCShift D 6 ) )
      )
      =
      (
        NTP4VCBase ( B ` ( NTP4VCShift D 5 ) )
      )
      /\
      (
        (
          B
          `
          (
            NTP4VCShift
              ( B ` ( NTP4VCShift D 3 ) )
              4
          )
        )
        =
        D
        /\
        (
          (
            B
            `
            (
              NTP4VCShift
                ( B ` ( NTP4VCShift D 4 ) )
                3
            )
          )
          =
          D
          /\
          (
            0 <_ ( C ` ( NTP4VCShift D 7 ) )
            /\
            (
              ( C ` ( NTP4VCShift D 7 ) )
              <
              ( C ` ( NTP4VCShift D 9 ) )
              /\
              (
                0 <_ ( C ` ( NTP4VCShift D 8 ) )
                /\
                (
                  ( C ` ( NTP4VCShift D 8 ) )
                  <
                  ( C ` ( NTP4VCShift D 9 ) )
                  /\
                  (
                    ( NTP4VCValidRW A D NTP4VCFileSize )
                    /\
                    (
                      NTP4VCAddrLe
                        P
                        ( B ` ( NTP4VCShift D 5 ) )
                        ( B ` ( NTP4VCShift D 6 ) )
                      /\
                      (
                        NTP4VCValidFile A C ( NTP4VCShift D 0 )
                        /\
                        (
                          NTP4VCSeparated
                            D NTP4VCFileSize
                            ( B ` ( NTP4VCShift D 4 ) )
                            NTP4VCFileSize
                          /\
                          (
                            NTP4VCSeparated
                              D NTP4VCFileSize
                              ( B ` ( NTP4VCShift D 3 ) )
                              NTP4VCFileSize
                            /\
                            (
                              NTP4VCSeparated
                                ( B ` ( NTP4VCShift D 4 ) )
                                NTP4VCFileSize
                                ( B ` ( NTP4VCShift D 3 ) )
                                NTP4VCFileSize
                              /\
                              (
                                NTP4VCValidIOFileNoRec
                                  A B C
                                  ( B ` ( NTP4VCShift D 4 ) )
                                  P Q
                                /\
                                (
                                  NTP4VCValidIOFileNoRec
                                    A B C
                                    ( B ` ( NTP4VCShift D 3 ) )
                                    P Q
                                  /\
                                  (
                                    NTP4VCValidRW
                                      A
                                      (
                                        NTP4VCShift
                                          ( B ` ( NTP4VCShift D 5 ) )
                                          0
                                      )
                                      (
                                        NTP4VCHeaderSize
                                        +
                                        ( C ` ( NTP4VCShift D 9 ) )
                                      )
                                    /\
                                    (
                                      NTP4VCSeparated
                                        D NTP4VCFileSize
                                        (
                                          NTP4VCShift
                                            ( B ` ( NTP4VCShift D 5 ) )
                                            0
                                        )
                                        (
                                          NTP4VCHeaderSize
                                          +
                                          ( C ` ( NTP4VCShift D 9 ) )
                                        )
                                      /\
                                      (
                                        NTP4VCSeparated
                                          ( B ` ( NTP4VCShift D 4 ) )
                                          NTP4VCFileSize
                                          (
                                            NTP4VCShift
                                              ( B ` ( NTP4VCShift D 5 ) )
                                              0
                                          )
                                          (
                                            NTP4VCHeaderSize
                                            +
                                            ( C ` ( NTP4VCShift D 9 ) )
                                          )
                                        /\
                                        (
                                          NTP4VCSeparated
                                            ( B ` ( NTP4VCShift D 3 ) )
                                            NTP4VCFileSize
                                            (
                                              NTP4VCShift
                                                ( B ` ( NTP4VCShift D 5 ) )
                                                0
                                            )
                                            (
                                              NTP4VCHeaderSize
                                              +
                                              ( C ` ( NTP4VCShift D 9 ) )
                                            )
                                          /\
                                          (
                                            NTP4VCAddrLt
                                              Q
                                              (
                                                B
                                                `
                                                ( NTP4VCShift D 6 )
                                              )
                                              (
                                                NTP4VCShift
                                                  (
                                                    B
                                                    `
                                                    ( NTP4VCShift D 5 )
                                                  )
                                                  (
                                                    NTP4VCHeaderSize
                                                    +
                                                    (
                                                      C
                                                      `
                                                      ( NTP4VCShift D 9 )
                                                    )
                                                  )
                                              )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
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

${
  $d x y A B C D E F G H J K L M N O P Q R S T U V $.

  $( Source parameters:
     A=t_1, B=t_2, C=i_3, D=i_4, E=a_4, F=a_5, G=a_2, H=a,
     J=i_5, K=t_3, T=t, M=a_1, N=a_3, O=i, P=i_1, Q=i_2.
     R is region; L and S are the linked and sconst extensions; U and V are
     the addr_le and addr_lt extensions. Every source let, including the data,
     buffer, previous, next, input-byte, write-start, public-file, and
     updated-memory bindings, is expanded at its use site. $)

  ntp4vc-int-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-sconst-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i3-integer $e |- C e. ZZ $.
  ntp4vc-i4-integer $e |- D e. ZZ $.
  ntp4vc-a4-address $e |- E e. NTP4VCAddr $.
  ntp4vc-a5-address $e |- F e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- G e. NTP4VCAddr $.
  ntp4vc-a-address $e |- H e. NTP4VCAddr $.
  ntp4vc-i5-integer $e |- J e. ZZ $.
  ntp4vc-pointer-map $e |- K e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-a1-address $e |- M e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- N e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- O e. ZZ $.
  ntp4vc-i1-integer $e |- P e. ZZ $.
  ntp4vc-i2-integer $e |- Q e. ZZ $.

  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- U C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- V C_ ( NTP4VCAddr X. NTP4VCAddr ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe U x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-addr-lt-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLt V x y )
        <->
        ( NTP4VCOffset x ) < ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-i4-nonzero $e |- D =/= 0 $.
  ntp4vc-shifted-addresses-equal $e |- (
    ( NTP4VCShift G 0 ) = ( NTP4VCShift H 0 )
  ) $.
  ntp4vc-a5-mode-one $e |- (
    ( A ` ( NTP4VCShift F ; 1 0 ) ) = 1
  ) $.
  ntp4vc-buffer-size $e |- (
    ( A ` ( NTP4VCShift F 9 ) ) = NTP4VCBufferSize
  ) $.
  ntp4vc-data-buffer-same-base $e |- (
    (
      NTP4VCBase ( K ` ( NTP4VCShift F 6 ) )
    )
    =
    (
      NTP4VCBase ( K ` ( NTP4VCShift F 5 ) )
    )
  ) $.
  ntp4vc-previous-next-backlink $e |- (
    (
      K
      `
      (
        NTP4VCShift
          ( K ` ( NTP4VCShift F 4 ) )
          3
      )
    )
    =
    F
  ) $.
  ntp4vc-next-previous-backlink $e |- (
    (
      K
      `
      (
        NTP4VCShift
          ( K ` ( NTP4VCShift F 3 ) )
          4
      )
    )
    =
    F
  ) $.
  ntp4vc-previous-byte-ten $e |- (
    ( B ` ( NTP4VCShift E ( D - 1 ) ) ) = ; 1 0
  ) $.
  ntp4vc-output-byte-nonnegative $e |- 0 <_ O $.
  ntp4vc-i3-nonnegative $e |- 0 <_ C $.
  ntp4vc-i4-nonnegative $e |- 0 <_ D $.
  ntp4vc-i5-nonnegative $e |- 0 <_ J $.
  ntp4vc-sum-nonnegative $e |- 0 <_ ( C + D ) $.
  ntp4vc-input-bytes-nonnegative $e |- (
    0 <_ ( A ` ( NTP4VCShift F 7 ) )
  ) $.
  ntp4vc-region-a2 $e |- ( R ` ( NTP4VCBase G ) ) <_ 0 $.
  ntp4vc-region-a4 $e |- ( R ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-output-byte-buffer-bound $e |- (
    O <_ ( NTP4VCBufferSize - 1 )
  ) $.
  ntp4vc-input-bytes-buffer-bound $e |- (
    ( A ` ( NTP4VCShift F 7 ) ) <_ ( NTP4VCBufferSize - 1 )
  ) $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed R K ) $.
  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-sconst-int-memory $e |- B e. S $.
  ntp4vc-output-byte-uint32 $e |- ( NTP4VCUint32 O ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i4-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i5-uint32 $e |- ( NTP4VCUint32 J ) $.
  ntp4vc-file-record-valid-rw $e |- (
    NTP4VCValidRW T F NTP4VCFileSize
  ) $.
  ntp4vc-sum-uint32 $e |- ( NTP4VCUint32 ( C + D ) ) $.
  ntp4vc-input-bytes-uint32 $e |- (
    NTP4VCUint32 ( A ` ( NTP4VCShift F 7 ) )
  ) $.
  ntp4vc-a1-valid-io-file $e |- (
    NTP4VCValidIOFile T K A M U V
  ) $.
  ntp4vc-a3-valid-io-file $e |- (
    NTP4VCValidIOFile T K A N U V
  ) $.
  ntp4vc-a5-valid-io-file $e |- (
    NTP4VCValidIOFile T K A F U V
  ) $.
  ntp4vc-buffer-before-data $e |- (
    NTP4VCAddrLe
      U
      ( K ` ( NTP4VCShift F 5 ) )
      ( K ` ( NTP4VCShift F 6 ) )
  ) $.
  ntp4vc-a4-i4-valid-rw $e |- (
    NTP4VCValidRW T ( NTP4VCShift E 0 ) D
  ) $.
  ntp4vc-a4-sum-valid-rw $e |- (
    NTP4VCValidRW T ( NTP4VCShift E 0 ) ( C + D )
  ) $.
  ntp4vc-file-next-separated $e |- (
    NTP4VCSeparated
      F NTP4VCFileSize
      ( K ` ( NTP4VCShift F 3 ) ) NTP4VCFileSize
  ) $.
  ntp4vc-file-previous-separated $e |- (
    NTP4VCSeparated
      F NTP4VCFileSize
      ( K ` ( NTP4VCShift F 4 ) ) NTP4VCFileSize
  ) $.
  ntp4vc-next-previous-separated $e |- (
    NTP4VCSeparated
      ( K ` ( NTP4VCShift F 3 ) ) NTP4VCFileSize
      ( K ` ( NTP4VCShift F 4 ) ) NTP4VCFileSize
  ) $.
  ntp4vc-data-before-buffer-end $e |- (
    NTP4VCAddrLt
      V
      ( K ` ( NTP4VCShift F 6 ) )
      (
        NTP4VCShift
          ( K ` ( NTP4VCShift F 5 ) )
          ( NTP4VCHeaderSize + NTP4VCBufferSize )
      )
  ) $.
  ntp4vc-buffer-valid-rw $e |- (
    NTP4VCValidRW
      T
      ( NTP4VCShift ( K ` ( NTP4VCShift F 5 ) ) 0 )
      ( NTP4VCHeaderSize + NTP4VCBufferSize )
  ) $.
  ntp4vc-updated-public-file-valid $e |- (
    NTP4VCValidFile
      T
      (
        NTP4VCUpdate
          (
            NTP4VCUpdate
              (
                NTP4VCUpdate A ( NTP4VCShift F 8 ) O
              )
              ( NTP4VCShift ( NTP4VCShift F 0 ) 1 )
              P
          )
          ( NTP4VCShift ( NTP4VCShift F 0 ) 2 )
          Q
      )
      ( NTP4VCShift F 0 )
  ) $.
  ntp4vc-file-buffer-separated $e |- (
    NTP4VCSeparated
      F NTP4VCFileSize
      ( NTP4VCShift ( K ` ( NTP4VCShift F 5 ) ) 0 )
      ( NTP4VCHeaderSize + NTP4VCBufferSize )
  ) $.
  ntp4vc-next-buffer-separated $e |- (
    NTP4VCSeparated
      ( K ` ( NTP4VCShift F 3 ) ) NTP4VCFileSize
      ( NTP4VCShift ( K ` ( NTP4VCShift F 5 ) ) 0 )
      ( NTP4VCHeaderSize + NTP4VCBufferSize )
  ) $.
  ntp4vc-previous-buffer-separated $e |- (
    NTP4VCSeparated
      ( K ` ( NTP4VCShift F 4 ) ) NTP4VCFileSize
      ( NTP4VCShift ( K ` ( NTP4VCShift F 5 ) ) 0 )
      ( NTP4VCHeaderSize + NTP4VCBufferSize )
  ) $.
  ntp4vc-updated-next-valid-norec $e |- (
    NTP4VCValidIOFileNoRec
      T K
      (
        NTP4VCUpdate
          (
            NTP4VCUpdate
              (
                NTP4VCUpdate A ( NTP4VCShift F 8 ) O
              )
              ( NTP4VCShift ( NTP4VCShift F 0 ) 1 )
              P
          )
          ( NTP4VCShift ( NTP4VCShift F 0 ) 2 )
          Q
      )
      ( K ` ( NTP4VCShift F 3 ) ) U V
  ) $.
  ntp4vc-updated-previous-valid-norec $e |- (
    NTP4VCValidIOFileNoRec
      T K
      (
        NTP4VCUpdate
          (
            NTP4VCUpdate
              (
                NTP4VCUpdate A ( NTP4VCShift F 8 ) O
              )
              ( NTP4VCShift ( NTP4VCShift F 0 ) 1 )
              P
          )
          ( NTP4VCShift ( NTP4VCShift F 0 ) 2 )
          Q
      )
      ( K ` ( NTP4VCShift F 4 ) ) U V
  ) $.
  ntp4vc-intermediate-bytes-not-ten $e |- A. x e. ZZ
    (
      D < x
      ->
      (
        x <_ ( C + D )
        ->
        ( B ` ( NTP4VCShift E ( x - 1 ) ) ) =/= ; 1 0
      )
    ) $.

  ntp4vc-fwrite-call-fflush-pre-part4-goal16 $a |- (
    NTP4VCValidIOFile
      T
      K
      (
        NTP4VCUpdate
          (
            NTP4VCUpdate
              (
                NTP4VCUpdate
                  A
                  ( NTP4VCShift F 8 )
                  O
              )
              ( NTP4VCShift ( NTP4VCShift F 0 ) 1 )
              P
          )
          ( NTP4VCShift ( NTP4VCShift F 0 ) 2 )
          Q
      )
      F U V
  ) $.
$}
