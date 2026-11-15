$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_20
  (verina__metamath__verina_basic_20), catalog title uniqueProduct: the exact
  executable left-to-right hash-set scan multiplies each distinct integer of
  an arbitrary finite array at its first occurrence and satisfies the
  eraseDups-fold product correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer arrays and lists. The empty word (/), singleton
  word <" x ">, concatenation ++, range, reverse, length, and lookup give the
  corresponding finite-sequence operations. VERINAB20ToList is therefore the
  source Array.toList conversion extensionally.

  VERINAB20LoopGraph is the least relation closed under the three exact local
  loop branches after replacing the source index by the equivalent
  unprocessed suffix. The empty suffix returns the current integer product.
  For a nonempty suffix, membership of its head in ran seen is exactly
  Std.HashSet.contains: a repeated value leaves both seen and product
  unchanged, while a first occurrence inserts the value and multiplies the
  accumulator by it. Prepending a newly inserted value represents the hash
  set extensionally, since only contains and insert are observable.
  VERINAB20Loop selects the unique result, and VERINAB20UniqueProduct invokes
  it on the complete input with the empty seen set and product one. Thus the
  executable output is fixed independently of the postcondition and admits
  no additional results.

  VERINAB20EraseDupsAuxGraph is the exact first-occurrence-preserving
  List.eraseDupsBy loop: it scans left to right, skips values already in the
  seen accumulator, prepends each new value to both seen and output
  accumulators, and reverses the output accumulator at the end.
  VERINAB20EraseDups and VERINAB20Product then reproduce
  arr.toList.eraseDups.foldl (fun a b => a * b) 1 exactly.

  VERINAB20Pre is the source True precondition on typed Array Int inputs.
  VERINAB20Post preserves both source integer-subtraction equalities to zero.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB20ToList
  VERINAB20LoopGraph VERINAB20Loop
  VERINAB20Pre VERINAB20UniqueProduct
  VERINAB20EraseDupsAuxGraph VERINAB20EraseDupsAux VERINAB20EraseDups
  VERINAB20ProductGraph VERINAB20Product
  VERINAB20Post
$.

verinab20-to-list-syntax
  $a class ( VERINAB20ToList A ) $.
verinab20-loop-graph-syntax
  $a wff ( VERINAB20LoopGraph A B C D ) $.
verinab20-loop-syntax
  $a class ( VERINAB20Loop A B C ) $.
verinab20-precondition-syntax
  $a wff ( VERINAB20Pre A ) $.
verinab20-program-syntax
  $a class ( VERINAB20UniqueProduct A ) $.
verinab20-erase-dups-aux-graph-syntax
  $a wff ( VERINAB20EraseDupsAuxGraph A B C D ) $.
verinab20-erase-dups-aux-syntax
  $a class ( VERINAB20EraseDupsAux A B C ) $.
verinab20-erase-dups-syntax
  $a class ( VERINAB20EraseDups A ) $.
verinab20-product-graph-syntax
  $a wff ( VERINAB20ProductGraph A B ) $.
verinab20-product-syntax
  $a class ( VERINAB20Product A ) $.
verinab20-postcondition-syntax
  $a wff ( VERINAB20Post A B ) $.

verinab20-to-list-definition $a |- (
  VERINAB20ToList A
) = A $.

${
  $d R A B C D h t s p y $.

  verinab20-loop-graph-definition $a |- (
    VERINAB20LoopGraph A B C D
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      (
        C e. ZZ
        /\
        D e. ZZ
      )
    )
    /\
    A. R
      (
        (
          (
            A. s e. Word ZZ
              A. p e. ZZ
                <.
                  <. <. (/) , s >. , p >.
                  ,
                  p
                >. e. R
            /\
            A. h e. ZZ
              A. t e. Word ZZ
                A. s e. Word ZZ
                  A. p e. ZZ
                    A. y e. ZZ
                      (
                        (
                          h e. ran s
                          /\
                          <.
                            <. <. t , s >. , p >.
                            ,
                            y
                          >. e. R
                        )
                        ->
                        <.
                          <.
                            <. ( <" h "> ++ t ) , s >.
                            ,
                            p
                          >.
                          ,
                          y
                        >. e. R
                      )
          )
          /\
          A. h e. ZZ
            A. t e. Word ZZ
              A. s e. Word ZZ
                A. p e. ZZ
                  A. y e. ZZ
                    (
                      (
                        h e/ ran s
                        /\
                        <.
                          <.
                            <. t , ( <" h "> ++ s ) >.
                            ,
                            ( p x. h )
                          >.
                          ,
                          y
                        >. e. R
                      )
                      ->
                      <.
                        <.
                          <. ( <" h "> ++ t ) , s >.
                          ,
                          p
                        >.
                        ,
                        y
                      >. e. R
                    )
        )
        ->
        <. <. <. A , B >. , C >. , D >. e. R
      )
  ) $.
$}

${
  $d y A B C $.

  verinab20-loop-definition $a |- (
    VERINAB20Loop A B C
  ) = (
    iota_ y e. ZZ
      ( VERINAB20LoopGraph A B C y )
  ) $.
$}

verinab20-precondition-definition $a |- (
  VERINAB20Pre A
) <-> (
  A e. Word ZZ
) $.

verinab20-program-definition $a |- (
  VERINAB20UniqueProduct A
) = (
  VERINAB20Loop A (/) 1
) $.

${
  $d R A B C D h t s a y $.

  verinab20-erase-dups-aux-graph-definition $a |- (
    VERINAB20EraseDupsAuxGraph A B C D
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      (
        C e. Word ZZ
        /\
        D e. Word ZZ
      )
    )
    /\
    A. R
      (
        (
          (
            A. s e. Word ZZ
              A. a e. Word ZZ
                <.
                  <. <. (/) , s >. , a >.
                  ,
                  ( reverse ` a )
                >. e. R
            /\
            A. h e. ZZ
              A. t e. Word ZZ
                A. s e. Word ZZ
                  A. a e. Word ZZ
                    A. y e. Word ZZ
                      (
                        (
                          h e. ran s
                          /\
                          <.
                            <. <. t , s >. , a >.
                            ,
                            y
                          >. e. R
                        )
                        ->
                        <.
                          <.
                            <. ( <" h "> ++ t ) , s >.
                            ,
                            a
                          >.
                          ,
                          y
                        >. e. R
                      )
          )
          /\
          A. h e. ZZ
            A. t e. Word ZZ
              A. s e. Word ZZ
                A. a e. Word ZZ
                  A. y e. Word ZZ
                    (
                      (
                        h e/ ran s
                        /\
                        <.
                          <.
                            <. t , ( <" h "> ++ s ) >.
                            ,
                            ( <" h "> ++ a )
                          >.
                          ,
                          y
                        >. e. R
                      )
                      ->
                      <.
                        <.
                          <. ( <" h "> ++ t ) , s >.
                          ,
                          a
                        >.
                        ,
                        y
                      >. e. R
                    )
        )
        ->
        <. <. <. A , B >. , C >. , D >. e. R
      )
  ) $.
$}

${
  $d y A B C $.

  verinab20-erase-dups-aux-definition $a |- (
    VERINAB20EraseDupsAux A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB20EraseDupsAuxGraph A B C y )
  ) $.
$}

verinab20-erase-dups-definition $a |- (
  VERINAB20EraseDups A
) = (
  VERINAB20EraseDupsAux
    ( VERINAB20ToList A )
    (/)
    (/)
) $.

${
  $d k s A B $.

  verinab20-product-graph-definition $a |- (
    VERINAB20ProductGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. s e. Word ZZ
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 1
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = (
              ( s ` k ) x. ( A ` k )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verinab20-product-definition $a |- (
    VERINAB20Product A
  ) = (
    iota_ y e. ZZ
      ( VERINAB20ProductGraph A y )
  ) $.
$}

verinab20-postcondition-definition $a |- (
  VERINAB20Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  (
    (
      B
      -
      (
        VERINAB20Product
          ( VERINAB20EraseDups A )
      )
    ) = 0
    /\
    (
      (
        VERINAB20Product
          ( VERINAB20EraseDups A )
      )
      -
      B
    ) = 0
  )
) $.

verina-basic-20-unique-product $a |- A. w e. Word ZZ
  (
    ( VERINAB20Pre w )
    ->
    (
      VERINAB20Post
        w
        ( VERINAB20UniqueProduct w )
    )
  )
$.
