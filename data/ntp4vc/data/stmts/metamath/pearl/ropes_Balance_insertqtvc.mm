$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/ropes_Balance_insertqtvc: the rope-queue insertion verification
  condition preserves rope invariants, unchanged lower queue entries, and
  concatenated-string semantics across its direct-update and recursive
  carry branches. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A Why3 array of ropes is represented by an arbitrary finite SetMM word over
  the rope carrier. NTP4VCToNat, NTP4VCAt, and NTP4VCSet reproduce the source
  integer-to-natural conversion, totalized list lookup, and list update.
  NTP4VCUpdateEq is the pointwise form of the source function-update equality.

  The three rope constructors are injective, disjoint tagged ordered pairs.
  Constructor closure, exhaustiveness, and structural induction characterize
  exactly the finite inductive rope type. The arbitrary inhabited character
  and string carriers, all immutable-string operations and laws, and the
  complete recursive rope length, invariant, and string definitions are
  retained explicitly.

  Fibonacci, max, and string_of_array retain their full integer and
  finite-array domains. NTP4VCStringEq expands the source extensional string
  equality, and NTP4VCAllInv preserves the bounded universal queue invariant.
  Let-bound values are replaced by direct substitution. The proposition-valued
  conditional is represented by its equivalent exhaustive guarded cases.

  Splitting the ambient source theory, typed theorem parameters, and theorem
  assumptions into scoped essential hypotheses is the curried Metamath sequent
  corresponding to the source theorem. The final $a declaration is Metamath's
  native unproved statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCEmp NTP4VCStr NTP4VCApp
  NTP4VCStrIndex NTP4VCStrAppend NTP4VCStrSub
  NTP4VCSOA
  NTP4VCToNat NTP4VCAt NTP4VCSet
  NTP4VCStringEq NTP4VCAllInv NTP4VCUpdateEq
$.

ntp4vc-emp-syntax $a class NTP4VCEmp $.
ntp4vc-str-syntax $a class ( NTP4VCStr A B C ) $.
ntp4vc-app-syntax $a class ( NTP4VCApp A B C ) $.
ntp4vc-str-index-syntax $a class ( NTP4VCStrIndex A B C ) $.
ntp4vc-str-append-syntax $a class ( NTP4VCStrAppend A B C ) $.
ntp4vc-str-sub-syntax $a class ( NTP4VCStrSub A B C D ) $.
ntp4vc-soa-syntax $a class ( NTP4VCSOA A B C D ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.

ntp4vc-string-eq-syntax
  $a wff ( NTP4VCStringEq A B C D ) $.
ntp4vc-all-inv-syntax
  $a wff ( NTP4VCAllInv A B C D E ) $.
ntp4vc-update-eq-syntax
  $a wff ( NTP4VCUpdateEq A B C D ) $.

ntp4vc-emp-def $a |- NTP4VCEmp = <. 0 , 0 >. $.

ntp4vc-str-def $a |- ( NTP4VCStr A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-app-def $a |- ( NTP4VCApp A B C ) =
  <. 2 , <. A , <. B , C >. >. >. $.

ntp4vc-str-index-def $a |- ( NTP4VCStrIndex A B C ) =
  ( C ` <. A , B >. ) $.

ntp4vc-str-append-def $a |- ( NTP4VCStrAppend A B C ) =
  ( C ` <. A , B >. ) $.

ntp4vc-str-sub-def $a |- ( NTP4VCStrSub A B C D ) =
  ( D ` <. <. A , B >. , C >. ) $.

ntp4vc-soa-def $a |- ( NTP4VCSOA A B C D ) =
  ( D ` <. <. A , B >. , C >. ) $.

ntp4vc-to-nat-def $a |- ( NTP4VCToNat A ) =
  if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-def $a |- ( NTP4VCAt A B C ) =
  if (
    ( NTP4VCToNat B ) < ( # ` A ) ,
    ( A ` ( NTP4VCToNat B ) ) ,
    C
  ) $.

${
  $d k A B C $.

  ntp4vc-set-def $a |- ( NTP4VCSet A B C ) =
    (
      k e. ( 0 ..^ ( # ` A ) ) |->
        if (
          k = ( NTP4VCToNat B ) ,
          C ,
          ( A ` k )
        )
    ) $.
$}

${
  $d i A B C D $.

  ntp4vc-string-eq-def $a |- (
    ( NTP4VCStringEq A B C D )
    <->
    (
      ( C ` A ) = ( C ` B )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( C ` A )
          )
          ->
          (
            NTP4VCStrIndex A i D
          )
          =
          (
            NTP4VCStrIndex B i D
          )
        )
    )
  ) $.
$}

${
  $d j A B C D E $.

  ntp4vc-all-inv-def $a |- (
    ( NTP4VCAllInv A B C D E )
    <->
    A. j e. ZZ
      (
        (
          B <_ j
          /\
          j <_ C
        )
        ->
        ( NTP4VCAt A j E ) e. D
      )
  ) $.
$}

${
  $d z A B C D $.

  ntp4vc-update-eq-def $a |- (
    ( NTP4VCUpdateEq A B C D )
    <->
    A. z e. ZZ
      (
        NTP4VCAt
          ( NTP4VCSet A B C )
          z D
      )
      =
      if (
        z = B ,
        C ,
        ( NTP4VCAt A z D )
      )
  ) $.
$}

${
  $d i j k l n o p q r s t u v w x y z
     A B C D E F G H I J K L M N O P Q R $.

  $( Source character and immutable-string theory. $)
  ntp4vc-char-carrier-nonempty $e |- A =/= (/) $.
  ntp4vc-string-carrier-nonempty $e |- B =/= (/) $.
  ntp4vc-string-length-function $e |- D e. ( ZZ ^m B ) $.
  ntp4vc-string-index-function
    $e |- E e. ( A ^m ( B X. ZZ ) ) $.
  ntp4vc-empty-string-type $e |- F e. B $.
  ntp4vc-string-append-function
    $e |- G e. ( B ^m ( B X. B ) ) $.
  ntp4vc-string-sub-function
    $e |- H e. ( B ^m ( ( B X. ZZ ) X. ZZ ) ) $.

  ntp4vc-string-length-nonnegative $e |- A. s e. B
    0 <_ ( D ` s ) $.

  ntp4vc-empty-string-length $e |- ( D ` F ) = 0 $.

  ntp4vc-string-extensionality $e |- A. s e. B A. t e. B
    (
      ( NTP4VCStringEq s t D E )
      ->
      s = t
    ) $.

  ntp4vc-string-append-length $e |- A. s e. B A. t e. B
    (
      D ` ( NTP4VCStrAppend s t G )
    )
    =
    (
      ( D ` s )
      +
      ( D ` t )
    ) $.

  ntp4vc-string-append-left $e |- A. s e. B A. t e. B
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( D ` s )
        )
        ->
        (
          NTP4VCStrIndex
            ( NTP4VCStrAppend s t G )
            i E
        )
        =
        ( NTP4VCStrIndex s i E )
      ) $.

  ntp4vc-string-append-right $e |- A. s e. B A. t e. B
    A. i e. ZZ
      (
        (
          ( D ` s ) <_ i
          /\
          i < ( ( D ` s ) + ( D ` t ) )
        )
        ->
        (
          NTP4VCStrIndex
            ( NTP4VCStrAppend s t G )
            i E
        )
        =
        (
          NTP4VCStrIndex
            t
            ( i - ( D ` s ) )
            E
        )
      ) $.

  ntp4vc-string-sub-length $e |- A. s e. B A. o e. ZZ
    A. n e. ZZ
      (
        (
          (
            (
              0 <_ n
              /\
              0 <_ o
            )
            /\
            o <_ ( D ` s )
          )
          /\
          ( o + n ) <_ ( D ` s )
        )
        ->
        (
          D ` ( NTP4VCStrSub s o n H )
        )
        =
        n
      ) $.

  ntp4vc-string-sub-index $e |- A. s e. B A. o e. ZZ
    A. n e. ZZ
      (
        (
          (
            (
              0 <_ n
              /\
              0 <_ o
            )
            /\
            o <_ ( D ` s )
          )
          /\
          ( o + n ) <_ ( D ` s )
        )
        ->
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < n
            )
            ->
            (
              NTP4VCStrIndex
                ( NTP4VCStrSub s o n H )
                i E
            )
            =
            ( NTP4VCStrIndex s ( o + i ) E )
          )
      ) $.

  $( Exact finite inductive rope carrier. $)
  ntp4vc-rope-emp-closure $e |- NTP4VCEmp e. C $.

  ntp4vc-rope-str-closure $e |- A. s e. B A. o e. ZZ A. n e. ZZ
    ( NTP4VCStr s o n ) e. C $.

  ntp4vc-rope-app-closure $e |- A. x e. C A. y e. C A. n e. ZZ
    ( NTP4VCApp x y n ) e. C $.

  ntp4vc-rope-constructor-exhaustive $e |- A. r e. C
    (
      r = NTP4VCEmp
      \/
      (
        E. s e. B E. o e. ZZ E. n e. ZZ
          r = ( NTP4VCStr s o n )
        \/
        E. x e. C E. y e. C E. n e. ZZ
          r = ( NTP4VCApp x y n )
      )
    ) $.

  ntp4vc-rope-structural-induction $e |- A. u e. ~P C
    (
      (
        NTP4VCEmp e. u
        /\
        (
          A. s e. B A. o e. ZZ A. n e. ZZ
            ( NTP4VCStr s o n ) e. u
          /\
          A. x e. C A. y e. C A. n e. ZZ
            (
              (
                x e. u
                /\
                y e. u
              )
              ->
              ( NTP4VCApp x y n ) e. u
            )
        )
      )
      ->
      u = C
    ) $.

  $( Complete source recursive definitions on ropes. $)
  ntp4vc-rope-length-function $e |- I e. ( ZZ ^m C ) $.
  ntp4vc-rope-invariant-predicate $e |- J C_ C $.
  ntp4vc-rope-string-function $e |- K e. ( B ^m C ) $.

  ntp4vc-rope-length-emp $e |- ( I ` NTP4VCEmp ) = 0 $.

  ntp4vc-rope-length-str $e |- A. s e. B A. o e. ZZ A. n e. ZZ
    (
      I ` ( NTP4VCStr s o n )
    )
    =
    n $.

  ntp4vc-rope-length-app $e |- A. x e. C A. y e. C A. n e. ZZ
    (
      I ` ( NTP4VCApp x y n )
    )
    =
    n $.

  ntp4vc-rope-invariant-emp $e |- NTP4VCEmp e. J $.

  ntp4vc-rope-invariant-str $e |- A. s e. B A. o e. ZZ
    A. n e. ZZ
      (
        ( NTP4VCStr s o n ) e. J
        <->
        (
          0 < n
          /\
          (
            (
              0 <_ o
              /\
              o < ( D ` s )
            )
            /\
            ( o + n ) <_ ( D ` s )
          )
        )
      ) $.

  ntp4vc-rope-invariant-app $e |- A. x e. C A. y e. C
    A. n e. ZZ
      (
        ( NTP4VCApp x y n ) e. J
        <->
        (
          0 < ( I ` x )
          /\
          (
            x e. J
            /\
            (
              0 < ( I ` y )
              /\
              (
                y e. J
                /\
                n = ( ( I ` x ) + ( I ` y ) )
              )
            )
          )
        )
      ) $.

  ntp4vc-rope-string-emp $e |- ( K ` NTP4VCEmp ) = F $.

  ntp4vc-rope-string-str $e |- A. s e. B A. o e. ZZ A. n e. ZZ
    (
      K ` ( NTP4VCStr s o n )
    )
    =
    ( NTP4VCStrSub s o n H ) $.

  ntp4vc-rope-string-app $e |- A. x e. C A. y e. C A. n e. ZZ
    (
      K ` ( NTP4VCApp x y n )
    )
    =
    (
      NTP4VCStrAppend
        ( K ` x )
        ( K ` y )
        G
    ) $.

  $( Why3 integer Fibonacci theory and Balance-module declarations. $)
  ntp4vc-fibonacci-function $e |- L e. ( ZZ ^m ZZ ) $.

  ntp4vc-fibonacci-definition $e |- A. n e. ZZ
    (
      0 <_ n
      ->
      (
        L ` n
      )
      =
      if
      (
        n = 0 ,
        0 ,
        if
        (
          n = 1 ,
          1 ,
          (
            ( L ` ( n - 1 ) )
            +
            ( L ` ( n - 2 ) )
          )
        )
      )
    ) $.

  ntp4vc-max-integer $e |- M e. ZZ $.
  ntp4vc-max-definition $e |- 2 <_ M $.

  ntp4vc-string-of-array-function
    $e |- N e. ( B ^m ( ( Word C X. ZZ ) X. ZZ ) ) $.

  ntp4vc-string-of-array-empty $e |- A. q e. Word C A. l e. ZZ
    (
      (
        0 <_ l
        /\
        l <_ ( # ` q )
      )
      ->
      (
        NTP4VCStringEq
          ( NTP4VCSOA q l l N )
          F D E
      )
    ) $.

  ntp4vc-string-of-array-concat-left $e |- A. q e. Word C
    A. l e. ZZ A. n e. ZZ
      (
        (
          (
            0 <_ l
            /\
            l < n
          )
          /\
          n <_ ( # ` q )
        )
        ->
        (
          NTP4VCStringEq
            ( NTP4VCSOA q l n N )
            (
              NTP4VCStrAppend
                ( NTP4VCSOA q ( l + 1 ) n N )
                ( K ` ( NTP4VCAt q l Q ) )
                G
            )
            D E
        )
      ) $.

  $( Source theorem parameters i, q, and r and their six assumptions. $)
  ntp4vc-i-integer $e |- R e. ZZ $.
  ntp4vc-q-array $e |- O e. Word C $.
  ntp4vc-r-rope $e |- P e. C $.
  ntp4vc-default-rope $e |- Q e. C $.
  ntp4vc-fact0 $e |- 2 <_ R $.
  ntp4vc-fact1 $e |- R < ( # ` O ) $.
  ntp4vc-fact2 $e |- ( # ` O ) = ( M + 1 ) $.
  ntp4vc-fact3 $e |- P e. J $.
  ntp4vc-fact4 $e |- ( NTP4VCAllInv O 2 M J Q ) $.
  ntp4vc-fact5 $e |- (
    (
      D ` ( NTP4VCSOA O R ( M + 1 ) N )
    )
    +
    ( I ` P )
  )
  <
  ( L ` ( M + 1 ) ) $.

  ntp4vc-pearl-ropes-balance-insert-vc $a |- (
    0 <_ R
    /\
    (
      R < ( # ` O )
      /\
      (
        (
          ( NTP4VCAt O R Q ) e. J
          /\
          P e. J
        )
        /\
        A. x e. C
          (
            (
              x e. J
              /\
              (
                NTP4VCStringEq
                  ( K ` x )
                  (
                    NTP4VCStrAppend
                      ( K ` ( NTP4VCAt O R Q ) )
                      ( K ` P )
                      G
                  )
                  D E
              )
            )
            ->
            (
              0 <_ ( R + 1 )
              /\
              (
                (
                  ( I ` x ) < ( L ` ( R + 1 ) )
                  /\
                  (
                    (
                      0 <_ R
                      /\
                      R < ( # ` O )
                    )
                    /\
                    (
                      (
                        ( # ` ( NTP4VCSet O R x ) )
                        =
                        ( # ` O )
                      )
                      ->
                      (
                        ( NTP4VCUpdateEq O R x Q )
                        ->
                        (
                          (
                            NTP4VCAllInv
                              ( NTP4VCSet O R x )
                              2 M J Q
                          )
                          /\
                          (
                            A. j e. ZZ
                              (
                                (
                                  2 <_ j
                                  /\
                                  j < R
                                )
                                ->
                                (
                                  NTP4VCAt
                                    ( NTP4VCSet O R x )
                                    j Q
                                )
                                =
                                ( NTP4VCAt O j Q )
                              )
                            /\
                            (
                              NTP4VCStringEq
                                (
                                  NTP4VCSOA
                                    ( NTP4VCSet O R x )
                                    R ( M + 1 ) N
                                )
                                (
                                  NTP4VCStrAppend
                                    ( NTP4VCSOA O R ( M + 1 ) N )
                                    ( K ` P )
                                    G
                                )
                                D E
                            )
                          )
                        )
                      )
                    )
                  )
                )
                \/
                (
                  -. ( ( I ` x ) < ( L ` ( R + 1 ) ) )
                  /\
                  (
                    (
                      0 <_ R
                      /\
                      R < ( # ` O )
                    )
                    /\
                    (
                      (
                        ( # ` ( NTP4VCSet O R NTP4VCEmp ) )
                        =
                        ( # ` O )
                      )
                      ->
                      (
                        ( NTP4VCUpdateEq O R NTP4VCEmp Q )
                        ->
                        (
                          (
                            (
                              (
                                0 <_ ( M - R )
                                /\
                                (
                                  M - ( R + 1 )
                                )
                                <
                                ( M - R )
                              )
                              /\
                              (
                                (
                                  2 <_ ( R + 1 )
                                  /\
                                  (
                                    R + 1
                                  )
                                  <
                                  (
                                    # `
                                    ( NTP4VCSet O R NTP4VCEmp )
                                  )
                                )
                                /\
                                (
                                  # `
                                  ( NTP4VCSet O R NTP4VCEmp )
                                )
                                =
                                ( M + 1 )
                              )
                            )
                            /\
                            (
                              x e. J
                              /\
                              (
                                (
                                  NTP4VCAllInv
                                    ( NTP4VCSet O R NTP4VCEmp )
                                    2 M J Q
                                )
                                /\
                                (
                                  (
                                    D `
                                    (
                                      NTP4VCSOA
                                        ( NTP4VCSet O R NTP4VCEmp )
                                        ( R + 1 ) ( M + 1 ) N
                                    )
                                  )
                                  +
                                  ( I ` x )
                                )
                                <
                                ( L ` ( M + 1 ) )
                              )
                            )
                          )
                          /\
                          A. q e. Word C
                            (
                              (
                                ( # ` q )
                                =
                                (
                                  # `
                                  ( NTP4VCSet O R NTP4VCEmp )
                                )
                              )
                              ->
                              (
                                (
                                  (
                                    NTP4VCAllInv q 2 M J Q
                                  )
                                  /\
                                  (
                                    A. j e. ZZ
                                      (
                                        (
                                          2 <_ j
                                          /\
                                          j < ( R + 1 )
                                        )
                                        ->
                                        (
                                          NTP4VCAt q j Q
                                        )
                                        =
                                        (
                                          NTP4VCAt
                                            (
                                              NTP4VCSet
                                                O R NTP4VCEmp
                                            )
                                            j Q
                                        )
                                      )
                                    /\
                                    (
                                      NTP4VCStringEq
                                        (
                                          NTP4VCSOA
                                            q ( R + 1 ) ( M + 1 ) N
                                        )
                                        (
                                          NTP4VCStrAppend
                                            (
                                              NTP4VCSOA
                                                (
                                                  NTP4VCSet
                                                    O R NTP4VCEmp
                                                )
                                                ( R + 1 ) ( M + 1 ) N
                                            )
                                            ( K ` x )
                                            G
                                        )
                                        D E
                                    )
                                  )
                                )
                                ->
                                (
                                  (
                                    NTP4VCAllInv q 2 M J Q
                                  )
                                  /\
                                  (
                                    A. j e. ZZ
                                      (
                                        (
                                          2 <_ j
                                          /\
                                          j < R
                                        )
                                        ->
                                        (
                                          NTP4VCAt q j Q
                                        )
                                        =
                                        ( NTP4VCAt O j Q )
                                      )
                                    /\
                                    (
                                      NTP4VCStringEq
                                        (
                                          NTP4VCSOA
                                            q R ( M + 1 ) N
                                        )
                                        (
                                          NTP4VCStrAppend
                                            (
                                              NTP4VCSOA
                                                O R ( M + 1 ) N
                                            )
                                            ( K ` P )
                                            G
                                        )
                                        D E
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
$}
