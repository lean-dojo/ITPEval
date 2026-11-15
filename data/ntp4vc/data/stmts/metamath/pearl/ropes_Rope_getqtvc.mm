$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/ropes_Rope_getqtvc: the rope character-access verification condition
  establishes valid recursive indices and consistency with the rope's modeled
  immutable string. This file contains no proof.
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
  Let-bound offsets are replaced by direct substitution, and each
  proposition-valued conditional is represented by its equivalent guarded
  disjunction. The universally quantified result character remains inside the
  second conjunct exactly as in the source verification condition.

  Splitting the ambient source theory, typed theorem parameters, and three
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

  $( Source theorem parameters r and i, followed by fact0--fact2. $)
  ntp4vc-r-rope $e |- L e. C $.
  ntp4vc-i-integer $e |- M e. ZZ $.
  ntp4vc-fact0 $e |- L e. J $.
  ntp4vc-fact1 $e |- 0 <_ M $.
  ntp4vc-fact2 $e |- M < ( I ` L ) $.

  ntp4vc-pearl-ropes-rope-get-vc $a |- (
    (
      (
        E. s e. B E. o e. ZZ E. n e. ZZ
          (
            L = ( NTP4VCStr s o n )
            /\
            (
              0 <_ ( o + M )
              /\
              ( o + M ) < ( D ` s )
            )
          )
        \/
        E. x e. C E. y e. C E. n e. ZZ
          (
            L = ( NTP4VCApp x y n )
            /\
            (
              (
                M < ( I ` x )
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
                      M < ( I ` x )
                    )
                  )
                )
              )
              \/
              (
                -. M < ( I ` x )
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
                      0 <_ ( M - ( I ` x ) )
                      /\
                      ( M - ( I ` x ) ) < ( I ` y )
                    )
                  )
                )
              )
            )
          )
      )
      /\
      A. q e. A
        (
          (
            (
              E. s e. B E. o e. ZZ E. n e. ZZ
                (
                  L = ( NTP4VCStr s o n )
                  /\
                  q = ( NTP4VCStrIndex s ( o + M ) E )
                )
              \/
              E. x e. C E. y e. C E. n e. ZZ
                (
                  L = ( NTP4VCApp x y n )
                  /\
                  (
                    (
                      M < ( I ` x )
                      /\
                      q = ( NTP4VCStrIndex ( K ` x ) M E )
                    )
                    \/
                    (
                      -. M < ( I ` x )
                      /\
                      q =
                        (
                          NTP4VCStrIndex
                            ( K ` y )
                            ( M - ( I ` x ) )
                            E
                        )
                    )
                  )
                )
            )
            ->
            q = ( NTP4VCStrIndex ( K ` L ) M E )
          )
        )
    )
  ) $.
$}
