$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/ropes_Rope_subqtvc: the rope substring verification condition
  establishes safe recursive sub-rope calls and preservation of the rope
  invariant and modeled substring semantics. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The character and immutable-string carriers remain arbitrary inhabited
  sets. Their integer length, indexing, empty string, append, and substring
  operations retain the complete source MyString laws.

  NTP4VCEmp, NTP4VCStr, and NTP4VCApp are disjoint injective tagged
  constructors. Closure, exhaustiveness, and structural induction characterize
  exactly the finite inductive rope type. Rope length, invariant, and modeled
  string retain their complete constructor equations over the full integer
  domain.

  The source matches are expanded into their exhaustive constructor cases.
  The let-bound left and right lengths are replaced by direct substitution,
  and each proposition-valued conditional is represented by its equivalent
  exhaustive guarded disjunction. The recursive-call result ropes remain
  universally quantified inside the safety obligation, while the final result
  rope remains universally quantified inside the postcondition obligation.
  The internal witnesses for the two recursive sub-ropes remain existentially
  quantified in the crossing-boundary branch.

  Splitting the ambient source theory, typed theorem parameters, and five
  theorem assumptions into scoped essential hypotheses is the curried
  Metamath sequent corresponding to the source theorem. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c
  NTP4VCEmp NTP4VCStr NTP4VCApp
  NTP4VCStrIndex NTP4VCStrAppend NTP4VCStrSub
  NTP4VCStringEq
$.

ntp4vc-emp-syntax $a class NTP4VCEmp $.
ntp4vc-str-syntax $a class ( NTP4VCStr A B C ) $.
ntp4vc-app-syntax $a class ( NTP4VCApp A B C ) $.
ntp4vc-str-index-syntax $a class ( NTP4VCStrIndex A B C ) $.
ntp4vc-str-append-syntax $a class ( NTP4VCStrAppend A B C ) $.
ntp4vc-str-sub-syntax $a class ( NTP4VCStrSub A B C D ) $.
ntp4vc-string-eq-syntax
  $a wff ( NTP4VCStringEq A B C D ) $.

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
  $d i n o q r s t u x y
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

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

  $( Source theorem parameters r, len, and ofs, followed by fact0--fact4. $)
  ntp4vc-r-rope $e |- L e. C $.
  ntp4vc-len-integer $e |- M e. ZZ $.
  ntp4vc-ofs-integer $e |- N e. ZZ $.
  ntp4vc-fact0 $e |- L e. J $.
  ntp4vc-fact1 $e |- 0 <_ M $.
  ntp4vc-fact2 $e |- 0 <_ N $.
  ntp4vc-fact3 $e |- N <_ ( I ` L ) $.
  ntp4vc-fact4 $e |- ( N + M ) <_ ( I ` L ) $.

  ntp4vc-pearl-ropes-rope-sub-vc $a |- (
    (
      (
        L = NTP4VCEmp
        \/
        (
          E. s e. B E. o e. ZZ E. n e. ZZ
            L = ( NTP4VCStr s o n )
          \/
          E. x e. C E. y e. C E. n e. ZZ
            (
              L = ( NTP4VCApp x y n )
              /\
              (
                (
                  ( M - ( ( I ` x ) - N ) ) <_ 0
                  /\
                  (
                    (
                      x = x
                      \/
                      y = x
                    )
                    /\
                    (
                      x e. J
                      /\
                      (
                        0 <_ M
                        /\
                        (
                          (
                            0 <_ N
                            /\
                            N <_ ( I ` x )
                          )
                          /\
                          ( N + M ) <_ ( I ` x )
                        )
                      )
                    )
                  )
                )
                \/
                (
                  -. ( M - ( ( I ` x ) - N ) ) <_ 0
                  /\
                  (
                    (
                      ( ( I ` x ) - N ) <_ 0
                      /\
                      (
                        (
                          x = y
                          \/
                          y = y
                        )
                        /\
                        (
                          y e. J
                          /\
                          (
                            0 <_ M
                            /\
                            (
                              (
                                0 <_ ( -u ( ( I ` x ) - N ) )
                                /\
                                ( -u ( ( I ` x ) - N ) ) <_ ( I ` y )
                              )
                              /\
                              (
                                ( -u ( ( I ` x ) - N ) ) + M
                              )
                              <_
                              ( I ` y )
                            )
                          )
                        )
                      )
                    )
                    \/
                    (
                      -. ( ( I ` x ) - N ) <_ 0
                      /\
                      (
                        (
                          (
                            x = y
                            \/
                            y = y
                          )
                          /\
                          (
                            y e. J
                            /\
                            (
                              0 <_ ( M - ( ( I ` x ) - N ) )
                              /\
                              (
                                (
                                  0 <_ 0
                                  /\
                                  0 <_ ( I ` y )
                                )
                                /\
                                (
                                  0 + ( M - ( ( I ` x ) - N ) )
                                )
                                <_
                                ( I ` y )
                              )
                            )
                          )
                        )
                        /\
                        A. q e. C
                          (
                            (
                              q e. J
                              /\
                              (
                                NTP4VCStringEq
                                  ( K ` q )
                                  (
                                    NTP4VCStrSub
                                      ( K ` y )
                                      0
                                      ( M - ( ( I ` x ) - N ) )
                                      H
                                  )
                                  D E
                              )
                            )
                            ->
                            (
                              (
                                (
                                  x = x
                                  \/
                                  y = x
                                )
                                /\
                                (
                                  x e. J
                                  /\
                                  (
                                    0 <_ ( ( I ` x ) - N )
                                    /\
                                    (
                                      (
                                        0 <_ N
                                        /\
                                        N <_ ( I ` x )
                                      )
                                      /\
                                      (
                                        N + ( ( I ` x ) - N )
                                      )
                                      <_
                                      ( I ` x )
                                    )
                                  )
                                )
                              )
                              /\
                              A. p e. C
                                (
                                  (
                                    p e. J
                                    /\
                                    (
                                      NTP4VCStringEq
                                        ( K ` p )
                                        (
                                          NTP4VCStrSub
                                            ( K ` x )
                                            N
                                            ( ( I ` x ) - N )
                                            H
                                        )
                                        D E
                                    )
                                  )
                                  ->
                                  (
                                    p e. J
                                    /\
                                    q e. J
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
      /\
      A. r e. C
        (
          (
            (
              (
                L = NTP4VCEmp
                /\
                r = NTP4VCEmp
              )
              \/
              (
                E. s e. B E. o e. ZZ E. n e. ZZ
                  (
                    L = ( NTP4VCStr s o n )
                    /\
                    (
                      (
                        M = 0
                        /\
                        r = NTP4VCEmp
                      )
                      \/
                      (
                        M =/= 0
                        /\
                        r = ( NTP4VCStr s ( o + N ) M )
                      )
                    )
                  )
                \/
                E. x e. C E. y e. C E. n e. ZZ
                  (
                    L = ( NTP4VCApp x y n )
                    /\
                    (
                      (
                        ( M - ( ( I ` x ) - N ) ) <_ 0
                        /\
                        (
                          r e. J
                          /\
                          (
                            NTP4VCStringEq
                              ( K ` r )
                              ( NTP4VCStrSub ( K ` x ) N M H )
                              D E
                          )
                        )
                      )
                      \/
                      (
                        -. ( M - ( ( I ` x ) - N ) ) <_ 0
                        /\
                        (
                          (
                            ( ( I ` x ) - N ) <_ 0
                            /\
                            (
                              r e. J
                              /\
                              (
                                NTP4VCStringEq
                                  ( K ` r )
                                  (
                                    NTP4VCStrSub
                                      ( K ` y )
                                      ( -u ( ( I ` x ) - N ) )
                                      M H
                                  )
                                  D E
                              )
                            )
                          )
                          \/
                          (
                            -. ( ( I ` x ) - N ) <_ 0
                            /\
                            E. q e. C
                              (
                                (
                                  q e. J
                                  /\
                                  (
                                    NTP4VCStringEq
                                      ( K ` q )
                                      (
                                        NTP4VCStrSub
                                          ( K ` y )
                                          0
                                          ( M - ( ( I ` x ) - N ) )
                                          H
                                      )
                                      D E
                                  )
                                )
                                /\
                                E. p e. C
                                  (
                                    (
                                      p e. J
                                      /\
                                      (
                                        NTP4VCStringEq
                                          ( K ` p )
                                          (
                                            NTP4VCStrSub
                                              ( K ` x )
                                              N
                                              ( ( I ` x ) - N )
                                              H
                                          )
                                          D E
                                      )
                                    )
                                    /\
                                    (
                                      r e. J
                                      /\
                                      (
                                        NTP4VCStringEq
                                          ( K ` r )
                                          (
                                            NTP4VCStrAppend
                                              ( K ` p )
                                              ( K ` q )
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
            ->
            (
              r e. J
              /\
              (
                NTP4VCStringEq
                  ( K ` r )
                  ( NTP4VCStrSub ( K ` L ) N M H )
                  D E
              )
            )
          )
        )
    )
  ) $.
$}
