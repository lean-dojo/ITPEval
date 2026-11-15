$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1149458
  (thousand-theorems__metamath__Q1149458), "Compactness theorem": an arbitrary
  first-order theory has a nonempty model if and only if every finite
  subtheory has a nonempty model. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A language is a pair of arity-indexed families of function and relation
  symbols. Terms and formulas are standard finite tagged-tree codes.
  Q1149458TermsAt L n contains exactly the terms whose free de Bruijn
  variables are below n. Q1149458FormulaLevels L contains <. n , p >.
  exactly when p is a formula with n available free variables; universal
  quantification changes level n + 1 to level n. Thus Q1149458Sentences L,
  the level-zero formulas, is precisely the set of closed sentences.

  A structure has a nonempty carrier and total interpretations of every
  symbol. Q1149458Eval and Q1149458Sat give compositional Tarski semantics.
  A theory is an arbitrary set of sentences. It is satisfiable when some
  nonempty structure models every sentence, and finitely satisfiable when
  each finite subset is satisfiable.

  Every declaration before the final one is syntax or a bidirectional
  definition required for this encoding. The final $a declaration is the
  single unproved corpus statement, and this database has no $p statement.
$)

$c Q1149458Language Q1149458FunKeys Q1149458RelKeys $.
$c Q1149458TermsAt Q1149458Terms Q1149458FormulaLevels $.
$c Q1149458Formulas Q1149458Sentences Q1149458Structure $.
$c Q1149458Eval Q1149458Sat Q1149458Theory Q1149458Model $.
$c Q1149458Satisfiable Q1149458FinitelySatisfiable $.

q1149458-language-syntax $a wff ( Q1149458Language L ) $.
q1149458-fun-keys-syntax $a class ( Q1149458FunKeys L ) $.
q1149458-rel-keys-syntax $a class ( Q1149458RelKeys L ) $.
q1149458-terms-at-syntax $a class ( Q1149458TermsAt L n ) $.
q1149458-terms-syntax $a class ( Q1149458Terms L ) $.
q1149458-formula-levels-syntax $a class ( Q1149458FormulaLevels L ) $.
q1149458-formulas-syntax $a class ( Q1149458Formulas L ) $.
q1149458-sentences-syntax $a class ( Q1149458Sentences L ) $.
q1149458-structure-syntax $a wff ( Q1149458Structure L M ) $.
q1149458-eval-syntax $a wff ( Q1149458Eval L M E ) $.
q1149458-sat-syntax $a wff ( Q1149458Sat L M E S ) $.
q1149458-theory-syntax $a wff ( Q1149458Theory L T ) $.
q1149458-model-syntax $a wff ( Q1149458Model L M T ) $.
q1149458-satisfiable-syntax $a wff ( Q1149458Satisfiable L T ) $.
q1149458-finitely-satisfiable-syntax $a
  wff ( Q1149458FinitelySatisfiable L T ) $.

${
  $d F L R $.

  q1149458-language-definition $a |- (
    ( Q1149458Language L )
    <->
    E. F E. R
      (
        L = <. F , R >.
        /\
        (
          F Fn NN0
          /\
          R Fn NN0
        )
      )
  ) $.
$}

${
  $d L k $.

  q1149458-fun-keys-definition $a |- (
    Q1149458FunKeys L
    =
    U_ k e. NN0
      ( { k } X. ( ( 1st ` L ) ` k ) )
  ) $.
$}

${
  $d L k $.

  q1149458-rel-keys-definition $a |- (
    Q1149458RelKeys L
    =
    U_ k e. NN0
      ( { k } X. ( ( 2nd ` L ) ` k ) )
  ) $.
$}

${
  $d A C L f i k n $.

  q1149458-terms-at-definition $a |- (
    Q1149458TermsAt L n
    =
    |^| { C |
      (
        A. i e. ( 0 ..^ n )
          <. 0 , i >. e. C
        /\
        A. k e. NN0
          A. f e. ( ( 1st ` L ) ` k )
            A. A e. ( C ^m ( 0 ..^ k ) )
              <. 1 , <. k , <. f , A >. >. >. e. C
      )
    }
  ) $.
$}

${
  $d L n $.

  q1149458-terms-definition $a |- (
    Q1149458Terms L
    =
    U_ n e. NN0 ( Q1149458TermsAt L n )
  ) $.
$}

${
  $d A C L k n p q r s t $.

  q1149458-formula-levels-definition $a |- (
    Q1149458FormulaLevels L
    =
    |^| { C |
      A. n e. NN0
        (
          A. k e. NN0
            A. r e. ( ( 2nd ` L ) ` k )
              A. A e. ( ( Q1149458TermsAt L n ) ^m ( 0 ..^ k ) )
                <.
                  n ,
                  <. 0 , <. k , <. r , A >. >. >.
                >. e. C
          /\
          (
            A. s e. ( Q1149458TermsAt L n )
              A. t e. ( Q1149458TermsAt L n )
                <. n , <. 1 , <. s , t >. >. >. e. C
            /\
            (
              <. n , <. 2 , 0 >. >. e. C
              /\
              (
                A. p A. q
                  (
                    (
                      <. n , p >. e. C
                      /\
                      <. n , q >. e. C
                    )
                    ->
                    <. n , <. 3 , <. p , q >. >. >. e. C
                  )
                /\
                A. p
                  (
                    <. ( n + 1 ) , p >. e. C
                    ->
                    <. n , <. 4 , p >. >. e. C
                  )
              )
            )
          )
        )
    }
  ) $.
$}

q1149458-formulas-definition $a |- (
  Q1149458Formulas L
  =
  ran ( Q1149458FormulaLevels L )
) $.

${
  $d L p $.

  q1149458-sentences-definition $a |- (
    Q1149458Sentences L
    =
    { p e. ( Q1149458Formulas L ) |
      <. 0 , p >. e. ( Q1149458FormulaLevels L )
    }
  ) $.
$}

${
  $d A F L M R X f k r $.

  q1149458-structure-definition $a |- (
    ( Q1149458Structure L M )
    <->
    (
      ( Q1149458Language L )
      /\
      E. X E. F E. R
        (
          M = <. X , <. F , R >. >.
          /\
          (
            X =/= ( / )
            /\
            (
              F Fn ( Q1149458FunKeys L )
              /\
              (
                R Fn ( Q1149458RelKeys L )
                /\
                (
                  A. k e. NN0
                    A. f e. ( ( 1st ` L ) ` k )
                      ( F ` <. k , f >. )
                        : ( X ^m ( 0 ..^ k ) ) --> X
                  /\
                  A. k e. NN0
                    A. r e. ( ( 2nd ` L ) ` k )
                      ( R ` <. k , r >. )
                        C_ ( X ^m ( 0 ..^ k ) )
                )
              )
            )
          )
        )
    )
  ) $.
$}

${
  $d A E L M V f i j k $.

  q1149458-eval-definition $a |- (
    ( Q1149458Eval L M E )
    <->
    (
      E :
        (
          ( ( 1st ` M ) ^m NN0 )
          X.
          ( Q1149458Terms L )
        )
        --> ( 1st ` M )
      /\
      (
        A. V e. ( ( 1st ` M ) ^m NN0 )
          A. i e. NN0
            ( E ` <. V , <. 0 , i >. >. ) = ( V ` i )
        /\
        A. V e. ( ( 1st ` M ) ^m NN0 )
          A. k e. NN0
            A. f e. ( ( 1st ` L ) ` k )
              A. A e. ( ( Q1149458Terms L ) ^m ( 0 ..^ k ) )
                (
                  E `
                    <. V , <. 1 , <. k , <. f , A >. >. >. >.
                )
                =
                (
                  (
                    ( 1st ` ( 2nd ` M ) )
                    ` <. k , f >.
                  )
                  `
                  (
                    j e. ( 0 ..^ k )
                    |->
                    ( E ` <. V , ( A ` j ) >. )
                  )
                )
      )
    )
  ) $.
$}

${
  $d A E L M S V j k n p q r s t x $.

  q1149458-sat-definition $a |- (
    ( Q1149458Sat L M E S )
    <->
    (
      S C_
        (
          ( ( 1st ` M ) ^m NN0 )
          X.
          ( Q1149458FormulaLevels L )
        )
      /\
      A. n e. NN0
        (
          A. V e. ( ( 1st ` M ) ^m NN0 )
            A. k e. NN0
              A. r e. ( ( 2nd ` L ) ` k )
                A. A e.
                  ( ( Q1149458TermsAt L n ) ^m ( 0 ..^ k ) )
                  (
                    <.
                      V ,
                      <.
                        n ,
                        <. 0 , <. k , <. r , A >. >. >.
                      >.
                    >. e. S
                    <->
                    (
                      j e. ( 0 ..^ k )
                      |->
                      ( E ` <. V , ( A ` j ) >. )
                    )
                    e.
                    (
                      ( 2nd ` ( 2nd ` M ) )
                      ` <. k , r >.
                    )
                  )
          /\
          (
            A. V e. ( ( 1st ` M ) ^m NN0 )
              A. s e. ( Q1149458TermsAt L n )
                A. t e. ( Q1149458TermsAt L n )
                  (
                    <. V , <. n , <. 1 , <. s , t >. >. >. >.
                      e. S
                    <->
                    ( E ` <. V , s >. ) = ( E ` <. V , t >. )
                  )
            /\
            (
              A. V e. ( ( 1st ` M ) ^m NN0 )
                -. <. V , <. n , <. 2 , 0 >. >. >. e. S
              /\
              (
                A. V e. ( ( 1st ` M ) ^m NN0 )
                  A. p A. q
                    (
                      (
                        <. n , p >. e. ( Q1149458FormulaLevels L )
                        /\
                        <. n , q >. e. ( Q1149458FormulaLevels L )
                      )
                      ->
                      (
                        <.
                          V ,
                          <. n , <. 3 , <. p , q >. >. >.
                        >. e. S
                        <->
                        (
                          <. V , <. n , p >. >. e. S
                          ->
                          <. V , <. n , q >. >. e. S
                        )
                      )
                    )
                /\
                A. V e. ( ( 1st ` M ) ^m NN0 )
                  A. p
                    (
                      <. ( n + 1 ) , p >.
                        e. ( Q1149458FormulaLevels L )
                      ->
                      (
                        <. V , <. n , <. 4 , p >. >. >. e. S
                        <->
                        A. x e. ( 1st ` M )
                          <.
                            (
                              j e. NN0
                              |->
                              if ( j = n , x , ( V ` j ) )
                            ) ,
                            <. ( n + 1 ) , p >.
                          >. e. S
                      )
                    )
              )
            )
          )
        )
    )
  ) $.
$}

q1149458-theory-definition $a |- (
  ( Q1149458Theory L T )
  <->
  T C_ ( Q1149458Sentences L )
) $.

${
  $d E L M S T V p $.

  q1149458-model-definition $a |- (
    ( Q1149458Model L M T )
    <->
    (
      (
        ( Q1149458Theory L T )
        /\
        ( Q1149458Structure L M )
      )
      /\
      E. E E. S
        (
          (
            ( Q1149458Eval L M E )
            /\
            ( Q1149458Sat L M E S )
          )
          /\
          A. p e. T
            A. V e. ( ( 1st ` M ) ^m NN0 )
              <. V , <. 0 , p >. >. e. S
        )
    )
  ) $.
$}

${
  $d L M T $.

  q1149458-satisfiable-definition $a |- (
    ( Q1149458Satisfiable L T )
    <->
    (
      ( Q1149458Theory L T )
      /\
      E. M ( Q1149458Model L M T )
    )
  ) $.
$}

${
  $d L T U $.

  q1149458-finitely-satisfiable-definition $a |- (
    ( Q1149458FinitelySatisfiable L T )
    <->
    (
      ( Q1149458Theory L T )
      /\
      A. U
        (
          (
            U e. Fin
            /\
            U C_ T
          )
          ->
          ( Q1149458Satisfiable L U )
        )
    )
  ) $.
$}

${
  $d L T $.

  thousand-theorems-q1149458-compactness $a |- (
    A. L A. T
      (
        (
          ( Q1149458Language L )
          /\
          ( Q1149458Theory L T )
        )
        ->
        (
          ( Q1149458Satisfiable L T )
          <->
          ( Q1149458FinitelySatisfiable L T )
        )
      )
  ) $.
$}
