$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/ropes_Balance_balanceqtvc: the rope-balancing verification condition
  for queue initialization, leaf insertion, and reconstruction of a valid
  rope with the same modeled string. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A Why3 array of ropes is represented by an arbitrary finite SetMM word over
  the rope carrier, with # giving its length and function application giving
  its zero-based entries. The three source rope constructors are injective,
  disjoint tagged ordered pairs. Constructor closure, exhaustiveness, and
  structural induction characterize exactly the finite inductive rope type,
  rather than a finite approximation or an uninterpreted collection of tags.

  The string carrier and character carrier remain arbitrary inhabited sets.
  Their length, indexing, empty string, append, and substring operations are
  total typed functions, and every source MyString axiom is an explicit
  hypothesis. Rope length, invariant, and modeled string are likewise given
  by their complete constructor equations. Fibonacci, max, and
  string_of_array retain their full integer and finite-array domains and all
  source defining laws used by this verification condition.

  NTP4VCStringEq expands the source extensional string equality.
  NTP4VCAllEmpty and NTP4VCAllInv preserve the source bounded universal
  quantifiers. NTP4VCLoopIndex, NTP4VCLoopResult, NTP4VCLoopObligation, and
  NTP4VCQueuePost are definitional groupings of the nested loop and queue
  obligations, with every rope, array, integer, and internal result quantifier
  at its original scope. Splitting the ambient source theory and the two
  theorem assumptions into scoped essential hypotheses is the curried
  Metamath sequent corresponding to the source theorem.

  The final $a declaration is Metamath's native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCEmp NTP4VCStr NTP4VCApp
  NTP4VCStrIndex NTP4VCStrAppend NTP4VCStrSub
  NTP4VCSOA NTP4VCSOQ
  NTP4VCStringEq NTP4VCAllEmpty NTP4VCAllInv
  NTP4VCLoopIndex NTP4VCLoopResult
  NTP4VCLoopObligation NTP4VCQueuePost
$.

ntp4vc-emp-syntax $a class NTP4VCEmp $.
ntp4vc-str-syntax $a class ( NTP4VCStr A B C ) $.
ntp4vc-app-syntax $a class ( NTP4VCApp A B C ) $.
ntp4vc-str-index-syntax $a class ( NTP4VCStrIndex A B C ) $.
ntp4vc-str-append-syntax $a class ( NTP4VCStrAppend A B C ) $.
ntp4vc-str-sub-syntax $a class ( NTP4VCStrSub A B C D ) $.
ntp4vc-soa-syntax $a class ( NTP4VCSOA A B C D ) $.
ntp4vc-soq-syntax $a class ( NTP4VCSOQ A B ) $.

ntp4vc-string-eq-syntax
  $a wff ( NTP4VCStringEq A B C D ) $.
ntp4vc-all-empty-syntax
  $a wff ( NTP4VCAllEmpty A B ) $.
ntp4vc-all-inv-syntax
  $a wff ( NTP4VCAllInv A B C D ) $.
ntp4vc-loop-index-syntax
  $a wff ( NTP4VCLoopIndex A B C D E F G H I J ) $.
ntp4vc-loop-result-syntax
  $a wff ( NTP4VCLoopResult A B C D E F G H I J K ) $.
ntp4vc-loop-obligation-syntax
  $a wff ( NTP4VCLoopObligation A B C D E F G H I J ) $.
ntp4vc-queue-post-syntax
  $a wff ( NTP4VCQueuePost A B C D E F G H I J K L ) $.

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

ntp4vc-soq-def $a |- ( NTP4VCSOQ A B ) =
  ( NTP4VCSOA A 2 ( # ` A ) B ) $.

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
  $d i A B $.

  ntp4vc-all-empty-def $a |- (
    ( NTP4VCAllEmpty A B )
    <->
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        ( A ` i ) = NTP4VCEmp
      )
  ) $.
$}

${
  $d j A B C D $.

  ntp4vc-all-inv-def $a |- (
    ( NTP4VCAllInv A B C D )
    <->
    A. j e. ZZ
      (
        (
          B <_ j
          /\
          j <_ C
        )
        ->
        ( A ` j ) e. D
      )
  ) $.
$}

${
  $d i o A B C D E F G H I J $.

  ntp4vc-loop-index-def $a |- (
    ( NTP4VCLoopIndex A B C D E F G H I J )
    <->
    A. i e. ZZ
      (
        (
          (
            (
              2 <_ i
              /\
              i <_ B
            )
            /\
            C e. E
          )
          /\
          (
            NTP4VCStringEq
              ( F ` C )
              ( NTP4VCSOA A 2 i G )
              I J
          )
        )
        ->
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          /\
          (
            (
              ( A ` i ) e. E
              /\
              C e. E
            )
            /\
            A. o e. D
              (
                (
                  o e. E
                  /\
                  (
                    NTP4VCStringEq
                      ( F ` o )
                      (
                        NTP4VCStrAppend
                          ( F ` ( A ` i ) )
                          ( F ` C )
                          H
                      )
                      I J
                  )
                )
                ->
                (
                  o e. E
                  /\
                  (
                    NTP4VCStringEq
                      ( F ` o )
                      ( NTP4VCSOA A 2 ( i + 1 ) G )
                      I J
                  )
                )
              )
          )
        )
      )
  ) $.
$}

ntp4vc-loop-result-def $a |- (
  ( NTP4VCLoopResult A B C D E F G H I J K )
  <->
  (
    ( NTP4VCLoopIndex A B C E F G H I J K )
    /\
    (
      (
        C e. F
        /\
        (
          NTP4VCStringEq
            ( G ` C )
            ( NTP4VCSOA A 2 ( B + 1 ) H )
            J K
        )
      )
      ->
      (
        C e. F
        /\
        (
          NTP4VCStringEq
            ( G ` C )
            ( G ` D )
            J K
        )
      )
    )
  )
) $.

${
  $d s A B C D E F G H I J $.

  ntp4vc-loop-obligation-def $a |- (
    ( NTP4VCLoopObligation A B C D E F G H I J )
    <->
    (
      (
        2 <_ ( B + 1 )
        ->
        (
          (
            NTP4VCEmp e. E
            /\
            (
              NTP4VCStringEq
                ( F ` NTP4VCEmp )
                ( NTP4VCSOA A 2 2 G )
                I J
            )
          )
          /\
          A. s e. D
            (
              NTP4VCLoopResult
                A B s C D E F G H I J
            )
        )
      )
      /\
      (
        ( B + 1 ) < 2
        ->
        (
          NTP4VCEmp e. E
          /\
          (
            NTP4VCStringEq
              ( F ` NTP4VCEmp )
              ( F ` C )
              I J
          )
        )
      )
    )
  ) $.
$}

${
  $d q A B C D E F G H I J K L $.

  ntp4vc-queue-post-def $a |- (
    ( NTP4VCQueuePost A B C D E F G H I J K L )
    <->
    (
      (
        (
          (
            (
              2 < ( # ` A )
              /\
              ( # ` A ) = ( C + 1 )
            )
            /\
            B e. E
          )
          /\
          ( NTP4VCAllInv A 2 C E )
        )
        /\
        (
          (
            K ` ( NTP4VCSOQ A I )
          )
          +
          ( F ` B )
        )
        <
        ( H ` ( C + 1 ) )
      )
      /\
      A. q e. Word D
        (
          ( # ` q ) = ( # ` A )
          ->
          (
            (
              ( NTP4VCAllInv q 2 C E )
              /\
              (
                NTP4VCStringEq
                  ( NTP4VCSOQ q I )
                  (
                    NTP4VCStrAppend
                      ( NTP4VCSOQ A I )
                      ( G ` B )
                      J
                  )
                  K L
              )
            )
            ->
            (
              NTP4VCLoopObligation
                q C B D E G I J K L
            )
          )
        )
    )
  ) $.
$}

${
  $d i j l n o q r s t u x y
     A B C D E F G H I J K L M N O $.

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
                ( K ` ( q ` l ) )
                G
            )
            D E
        )
      ) $.

  $( Source theorem parameter r and its two assumptions. $)
  ntp4vc-r-rope $e |- O e. C $.
  ntp4vc-fact0 $e |- O e. J $.
  ntp4vc-fact1 $e |- ( I ` O ) < ( L ` ( M + 1 ) ) $.

  ntp4vc-pearl-ropes-balance-vc $a |- (
    0 <_ ( M + 1 )
    /\
    A. q e. Word C
      (
        (
          ( NTP4VCAllEmpty q ( M + 1 ) )
          /\
          ( # ` q ) = ( M + 1 )
        )
        ->
        (
          NTP4VCQueuePost
            q O M C J I K L N G D E
        )
      )
  ) $.
$}
