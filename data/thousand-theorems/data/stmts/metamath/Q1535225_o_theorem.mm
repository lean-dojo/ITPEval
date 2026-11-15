$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1535225
  (thousand-theorems__metamath__Q1535225), catalog title
  "&#321;o&#347;' theorem" (ASCII: "Los' theorem"): a first-order
  sentence holds in an ultraproduct if and only if the set of component
  structures satisfying it belongs to the ultrafilter. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  A language is a pair of arity-indexed families of function and relation
  symbols. Terms and formulas are standard finite tagged-tree codes.
  Q1535225TermsAt L n contains exactly the terms whose free de Bruijn
  variables are below n. Q1535225FormulaLevels L contains <. n , p >.
  exactly when p is a formula with n available free variables; universal
  quantification changes level n + 1 to level n. Thus Q1535225Sentences L,
  the level-zero formulas, is precisely the set of closed sentences.

  A structure has a nonempty carrier and total interpretations of every
  symbol. Q1535225Eval and Q1535225Sat give compositional Tarski semantics,
  and Q1535225Models specializes them to closed sentences.

  Q1535225DepProduct is the full dependent product of the component carriers.
  Q1535225EqRel identifies two sections exactly when their equality set is in
  the ultrafilter. Q1535225Ultraproduct is the quotient carrier equipped with
  the pointwise function and relation interpretations; its definition
  explicitly quantifies representatives of quotient classes. Function values
  are full equivalence classes of pointwise outputs, and each relation binds
  one representative tuple before forming its ultrafilter truth set.

  Every declaration before the final one is syntax or a bidirectional
  definition required for this encoding. The final $a declaration is the
  single unproved corpus statement, and the root statement file contains no
  $p declaration.
$)

$c Q1535225Language Q1535225FunKeys Q1535225RelKeys $.
$c Q1535225TermsAt Q1535225Terms Q1535225FormulaLevels $.
$c Q1535225Formulas Q1535225Sentences Q1535225Structure $.
$c Q1535225Eval Q1535225Sat Q1535225Models Q1535225Family $.
$c Q1535225DepProduct Q1535225EqRel Q1535225IsUltraproduct $.
$c Q1535225Ultraproduct $.

q1535225-language-syntax $a wff ( Q1535225Language L ) $.
q1535225-fun-keys-syntax $a class ( Q1535225FunKeys L ) $.
q1535225-rel-keys-syntax $a class ( Q1535225RelKeys L ) $.
q1535225-terms-at-syntax $a class ( Q1535225TermsAt L n ) $.
q1535225-terms-syntax $a class ( Q1535225Terms L ) $.
q1535225-formula-levels-syntax $a class ( Q1535225FormulaLevels L ) $.
q1535225-formulas-syntax $a class ( Q1535225Formulas L ) $.
q1535225-sentences-syntax $a class ( Q1535225Sentences L ) $.
q1535225-structure-syntax $a wff ( Q1535225Structure L M ) $.
q1535225-eval-syntax $a wff ( Q1535225Eval L M E ) $.
q1535225-sat-syntax $a wff ( Q1535225Sat L M E S ) $.
q1535225-models-syntax $a wff ( Q1535225Models L M p ) $.
q1535225-family-syntax $a wff ( Q1535225Family L I M ) $.
q1535225-dependent-product-syntax $a class ( Q1535225DepProduct I M ) $.
q1535225-equivalence-relation-syntax $a class ( Q1535225EqRel I M U ) $.
q1535225-is-ultraproduct-syntax $a
  wff ( Q1535225IsUltraproduct L I M U P ) $.
q1535225-ultraproduct-syntax $a
  class ( Q1535225Ultraproduct L I M U ) $.

${
  $d F L R $.

  q1535225-language-definition $a |- (
    ( Q1535225Language L )
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

  q1535225-fun-keys-definition $a |- (
    Q1535225FunKeys L
    =
    U_ k e. NN0
      ( { k } X. ( ( 1st ` L ) ` k ) )
  ) $.
$}

${
  $d L k $.

  q1535225-rel-keys-definition $a |- (
    Q1535225RelKeys L
    =
    U_ k e. NN0
      ( { k } X. ( ( 2nd ` L ) ` k ) )
  ) $.
$}

${
  $d A C L f i k n $.

  q1535225-terms-at-definition $a |- (
    Q1535225TermsAt L n
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

  q1535225-terms-definition $a |- (
    Q1535225Terms L
    =
    U_ n e. NN0 ( Q1535225TermsAt L n )
  ) $.
$}

${
  $d A C L k n p q r s t $.

  q1535225-formula-levels-definition $a |- (
    Q1535225FormulaLevels L
    =
    |^| { C |
      A. n e. NN0
        (
          A. k e. NN0
            A. r e. ( ( 2nd ` L ) ` k )
              A. A e. ( ( Q1535225TermsAt L n ) ^m ( 0 ..^ k ) )
                <.
                  n ,
                  <. 0 , <. k , <. r , A >. >. >.
                >. e. C
          /\
          (
            A. s e. ( Q1535225TermsAt L n )
              A. t e. ( Q1535225TermsAt L n )
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

q1535225-formulas-definition $a |- (
  Q1535225Formulas L
  =
  ran ( Q1535225FormulaLevels L )
) $.

${
  $d L p $.

  q1535225-sentences-definition $a |- (
    Q1535225Sentences L
    =
    { p e. ( Q1535225Formulas L ) |
      <. 0 , p >. e. ( Q1535225FormulaLevels L )
    }
  ) $.
$}

${
  $d A F L M R X f k r $.

  q1535225-structure-definition $a |- (
    ( Q1535225Structure L M )
    <->
    (
      ( Q1535225Language L )
      /\
      E. X E. F E. R
        (
          M = <. X , <. F , R >. >.
          /\
          (
            X =/= ( / )
            /\
            (
              F Fn ( Q1535225FunKeys L )
              /\
              (
                R Fn ( Q1535225RelKeys L )
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

  q1535225-eval-definition $a |- (
    ( Q1535225Eval L M E )
    <->
    (
      E :
        (
          ( ( 1st ` M ) ^m NN0 )
          X.
          ( Q1535225Terms L )
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
              A. A e. ( ( Q1535225Terms L ) ^m ( 0 ..^ k ) )
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

  q1535225-sat-definition $a |- (
    ( Q1535225Sat L M E S )
    <->
    (
      S C_
        (
          ( ( 1st ` M ) ^m NN0 )
          X.
          ( Q1535225FormulaLevels L )
        )
      /\
      A. n e. NN0
        (
          A. V e. ( ( 1st ` M ) ^m NN0 )
            A. k e. NN0
              A. r e. ( ( 2nd ` L ) ` k )
                A. A e.
                  ( ( Q1535225TermsAt L n ) ^m ( 0 ..^ k ) )
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
              A. s e. ( Q1535225TermsAt L n )
                A. t e. ( Q1535225TermsAt L n )
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
                        <. n , p >. e. ( Q1535225FormulaLevels L )
                        /\
                        <. n , q >. e. ( Q1535225FormulaLevels L )
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
                        e. ( Q1535225FormulaLevels L )
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

${
  $d E L M S V p $.

  q1535225-models-definition $a |- (
    ( Q1535225Models L M p )
    <->
    (
      (
        ( Q1535225Structure L M )
        /\
        p e. ( Q1535225Sentences L )
      )
      /\
      E. E E. S
        (
          (
            ( Q1535225Eval L M E )
            /\
            ( Q1535225Sat L M E S )
          )
          /\
          A. V e. ( ( 1st ` M ) ^m NN0 )
            <. V , <. 0 , p >. >. e. S
        )
    )
  ) $.
$}

${
  $d I L M a $.

  q1535225-family-definition $a |- (
    ( Q1535225Family L I M )
    <->
    (
      M Fn I
      /\
      A. a e. I
        ( Q1535225Structure L ( M ` a ) )
    )
  ) $.
$}

${
  $d I M a g $.

  q1535225-dependent-product-definition $a |- (
    Q1535225DepProduct I M
    =
    { g e.
      (
        (
          U. ran
            ( a e. I |-> ( 1st ` ( M ` a ) ) )
        )
        ^m I
      )
      |
      A. a e. I
        ( g ` a ) e. ( 1st ` ( M ` a ) )
    }
  ) $.
$}

${
  $d I M U a g h $.

  q1535225-equivalence-relation-definition $a |- (
    Q1535225EqRel I M U
    =
    { <. g , h >. |
      (
        (
          g e. ( Q1535225DepProduct I M )
          /\
          h e. ( Q1535225DepProduct I M )
        )
        /\
        { a e. I | ( g ` a ) = ( h ` a ) } e. U
      )
    }
  ) $.
$}

${
  $d A F I L M P R U X Y a f g h j k r $.

  q1535225-is-ultraproduct-definition $a |- (
    ( Q1535225IsUltraproduct L I M U P )
    <->
    (
      ( Q1535225Structure L P )
      /\
      (
        ( 1st ` P )
        =
        (
          ( Q1535225DepProduct I M )
          /.
          ( Q1535225EqRel I M U )
        )
        /\
        (
          A. k e. NN0
            A. f e. ( ( 1st ` L ) ` k )
              A. A e.
                (
                  (
                    (
                      ( Q1535225DepProduct I M )
                      /.
                      ( Q1535225EqRel I M U )
                    )
                    ^m ( 0 ..^ k )
                  )
                )
                (
                  (
                    (
                      ( 1st ` ( 2nd ` P ) )
                      ` <. k , f >.
                    )
                    ` A
                  )
                  =
                  { h e. ( Q1535225DepProduct I M ) |
                    E. X e.
                      (
                        ( Q1535225DepProduct I M )
                        ^m ( 0 ..^ k )
                      )
                      (
                        A. j e. ( 0 ..^ k )
                          ( X ` j ) e. ( A ` j )
                        /\
                        E. g e. ( Q1535225DepProduct I M )
                          (
                            A. a e. I
                              ( g ` a )
                              =
                              (
                                (
                                  (
                                    1st
                                    ` ( 2nd ` ( M ` a ) )
                                  )
                                  ` <. k , f >.
                                )
                                `
                                (
                                  j e. ( 0 ..^ k )
                                  |->
                                  ( ( X ` j ) ` a )
                                )
                              )
                            /\
                            <. g , h >.
                            e. ( Q1535225EqRel I M U )
                          )
                      )
                  }
                )
          /\
          A. k e. NN0
            A. r e. ( ( 2nd ` L ) ` k )
              A. A e.
                (
                  (
                    (
                      ( Q1535225DepProduct I M )
                      /.
                      ( Q1535225EqRel I M U )
                    )
                    ^m ( 0 ..^ k )
                  )
                )
                (
                  A
                  e.
                  (
                    (
                      2nd
                      ` ( 2nd ` P )
                    )
                    ` <. k , r >.
                  )
                  <->
                  E. X e.
                    (
                      ( Q1535225DepProduct I M )
                      ^m ( 0 ..^ k )
                    )
                    (
                      A. j e. ( 0 ..^ k )
                        ( X ` j ) e. ( A ` j )
                      /\
                      { a e. I |
                        (
                          j e. ( 0 ..^ k )
                          |->
                          ( ( X ` j ) ` a )
                        )
                        e.
                        (
                          (
                            2nd
                            ` ( 2nd ` ( M ` a ) )
                          )
                          ` <. k , r >.
                        )
                      } e. U
                    )
                )
        )
      )
    )
  ) $.
$}

${
  $d I L M P U $.

  q1535225-ultraproduct-definition $a |- (
    Q1535225Ultraproduct L I M U
    =
    ( iota P ( Q1535225IsUltraproduct L I M U P ) )
  ) $.
$}

${
  $d I L M U a p $.

  thousand-theorems-q1535225-los $a |- (
    A. L A. I A. M A. U A. p
      (
        (
          (
            ( Q1535225Language L )
            /\
            ( Q1535225Family L I M )
          )
          /\
          (
            U e. ( UFil ` I )
            /\
            p e. ( Q1535225Sentences L )
          )
        )
        ->
        (
          (
            Q1535225Models
              L
              ( Q1535225Ultraproduct L I M U )
              p
          )
          <->
          { a e. I |
            ( Q1535225Models L ( M ` a ) p )
          } e. U
        )
      )
  ) $.
$}
