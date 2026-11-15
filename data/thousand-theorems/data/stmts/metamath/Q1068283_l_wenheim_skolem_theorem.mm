$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1068283
  (thousand-theorems__metamath__Q1068283),
  "L&ouml;wenheim&ndash;Skolem theorem": for an
  arbitrary first-order language, infinite structure, and infinite cardinal
  at least the size of the language, there is a structure of that cardinality
  with an elementary embedding in one direction between the two structures.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A language L is encoded by a pair of arity-indexed families of function and
  relation symbols. Q1068283FunKeys L and Q1068283RelKeys L are their dependent
  sums over NN0, and Q1068283Symbols L is their tagged disjoint union. Thus its
  cardinality is exactly Mathlib's Language.card.

  A structure is a nonempty carrier together with total interpretations of
  every function symbol and relation symbol. Terms and formulas use standard
  finite tagged-tree codes and are defined as the least sets closed under the
  variable, application, atomic, false, implication, and universal-quantifier
  constructors. Q1068283Eval and Q1068283Sat give the corresponding
  compositional Tarski semantics.

  Q1068283ElemEmb L M N H says that H is injective from the carrier of M to
  the carrier of N and preserves truth of every formula under every variable
  assignment. This is equivalent to an elementary embedding; preservation of
  atomic formulas also forces preservation of all interpreted functions and
  relations.

  The cardinal K is represented by its initial ordinal, expressed by
  ( card ` K ) = K. The relations _om ~<_ K and Q1068283Symbols L ~<_ K encode
  aleph_0 <= K and L.card <= K. The final declaration is the single unproved
  corpus $a statement. All preceding $a declarations are syntax or faithful
  definitions, and this database contains no $p proof statement.
$)

$c Q1068283Language Q1068283FunKeys Q1068283RelKeys Q1068283Symbols $.
$c Q1068283Terms Q1068283Formulas Q1068283Structure $.
$c Q1068283Eval Q1068283Sat Q1068283ElemEmb $.

q1068283-language-syntax $a wff ( Q1068283Language L ) $.
q1068283-fun-keys-syntax $a class ( Q1068283FunKeys L ) $.
q1068283-rel-keys-syntax $a class ( Q1068283RelKeys L ) $.
q1068283-symbols-syntax $a class ( Q1068283Symbols L ) $.
q1068283-terms-syntax $a class ( Q1068283Terms L ) $.
q1068283-formulas-syntax $a class ( Q1068283Formulas L ) $.
q1068283-structure-syntax $a wff ( Q1068283Structure L M ) $.
q1068283-eval-syntax $a wff ( Q1068283Eval L M E ) $.
q1068283-sat-syntax $a wff ( Q1068283Sat L M E S ) $.
q1068283-elementary-embedding-syntax $a
  wff ( Q1068283ElemEmb L M N H ) $.

${
  $d F L R $.

  q1068283-language-definition $a |- (
    ( Q1068283Language L )
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
  $d L n $.

  q1068283-fun-keys-definition $a |- (
    Q1068283FunKeys L
    =
    U_ n e. NN0
      ( { n } X. ( ( 1st ` L ) ` n ) )
  ) $.
$}

${
  $d L n $.

  q1068283-rel-keys-definition $a |- (
    Q1068283RelKeys L
    =
    U_ n e. NN0
      ( { n } X. ( ( 2nd ` L ) ` n ) )
  ) $.
$}

q1068283-symbols-definition $a |- (
  Q1068283Symbols L
  =
  ( Q1068283FunKeys L |_| Q1068283RelKeys L )
) $.

${
  $d A C L f i n $.

  q1068283-terms-definition $a |- (
    Q1068283Terms L
    =
    |^| { C |
      (
        A. i e. NN0
          <. 0 , i >. e. C
        /\
        A. n e. NN0
          A. f e. ( ( 1st ` L ) ` n )
            A. A e. ( C ^m ( 0 ..^ n ) )
              <. 1 , <. n , <. f , A >. >. >. e. C
      )
    }
  ) $.
$}

${
  $d A C L i n p q r s t $.

  q1068283-formulas-definition $a |- (
    Q1068283Formulas L
    =
    |^| { C |
      (
        A. n e. NN0
          A. r e. ( ( 2nd ` L ) ` n )
            A. A e. ( ( Q1068283Terms L ) ^m ( 0 ..^ n ) )
              <. 0 , <. n , <. r , A >. >. >. e. C
        /\
        (
          A. s e. ( Q1068283Terms L )
            A. t e. ( Q1068283Terms L )
              <. 1 , <. s , t >. >. e. C
          /\
          (
            <. 2 , 0 >. e. C
            /\
            (
              A. p e. C A. q e. C
                <. 3 , <. p , q >. >. e. C
              /\
              A. i e. NN0 A. p e. C
                <. 4 , <. i , p >. >. e. C
            )
          )
        )
      )
    }
  ) $.
$}

${
  $d A F L M R X f n r $.

  q1068283-structure-definition $a |- (
    ( Q1068283Structure L M )
    <->
    (
      ( Q1068283Language L )
      /\
      E. X E. F E. R
        (
          M = <. X , <. F , R >. >.
          /\
          (
            X =/= ( / )
            /\
            (
              F Fn ( Q1068283FunKeys L )
              /\
              (
                R Fn ( Q1068283RelKeys L )
                /\
                (
                  A. n e. NN0
                    A. f e. ( ( 1st ` L ) ` n )
                      ( F ` <. n , f >. )
                        : ( X ^m ( 0 ..^ n ) ) --> X
                  /\
                  A. n e. NN0
                    A. r e. ( ( 2nd ` L ) ` n )
                      ( R ` <. n , r >. )
                        C_ ( X ^m ( 0 ..^ n ) )
                )
              )
            )
          )
        )
    )
  ) $.
$}

${
  $d A E L M V f i j n $.

  q1068283-eval-definition $a |- (
    ( Q1068283Eval L M E )
    <->
    (
      E :
        (
          ( ( ( 1st ` M ) ^m NN0 ) X. ( Q1068283Terms L ) )
        )
        --> ( 1st ` M )
      /\
      (
        A. V e. ( ( 1st ` M ) ^m NN0 )
          A. i e. NN0
            ( E ` <. V , <. 0 , i >. >. ) = ( V ` i )
        /\
        A. V e. ( ( 1st ` M ) ^m NN0 )
          A. n e. NN0
            A. f e. ( ( 1st ` L ) ` n )
              A. A e. ( ( Q1068283Terms L ) ^m ( 0 ..^ n ) )
                (
                  E `
                    <. V , <. 1 , <. n , <. f , A >. >. >. >.
                )
                =
                (
                  (
                    ( 1st ` ( 2nd ` M ) )
                    ` <. n , f >.
                  )
                  `
                  (
                    j e. ( 0 ..^ n )
                    |->
                    ( E ` <. V , ( A ` j ) >. )
                  )
                )
      )
    )
  ) $.
$}

${
  $d A E L M S V i j n p q r s t x $.

  q1068283-sat-definition $a |- (
    ( Q1068283Sat L M E S )
    <->
    (
      S C_
        (
          ( ( 1st ` M ) ^m NN0 )
          X.
          ( Q1068283Formulas L )
        )
      /\
      (
        A. V e. ( ( 1st ` M ) ^m NN0 )
          A. n e. NN0
            A. r e. ( ( 2nd ` L ) ` n )
              A. A e. ( ( Q1068283Terms L ) ^m ( 0 ..^ n ) )
                (
                  <.
                    V ,
                    <. 0 , <. n , <. r , A >. >. >.
                  >. e. S
                  <->
                  (
                    j e. ( 0 ..^ n )
                    |->
                    ( E ` <. V , ( A ` j ) >. )
                  )
                  e.
                  (
                    ( 2nd ` ( 2nd ` M ) )
                    ` <. n , r >.
                  )
                )
        /\
        (
          A. V e. ( ( 1st ` M ) ^m NN0 )
            A. s e. ( Q1068283Terms L )
              A. t e. ( Q1068283Terms L )
                (
                  <. V , <. 1 , <. s , t >. >. >. e. S
                  <->
                  ( E ` <. V , s >. ) = ( E ` <. V , t >. )
                )
          /\
          (
            A. V e. ( ( 1st ` M ) ^m NN0 )
              -. <. V , <. 2 , 0 >. >. e. S
            /\
            (
              A. V e. ( ( 1st ` M ) ^m NN0 )
                A. p e. ( Q1068283Formulas L )
                  A. q e. ( Q1068283Formulas L )
                    (
                      <. V , <. 3 , <. p , q >. >. >. e. S
                      <->
                      (
                        <. V , p >. e. S
                        ->
                        <. V , q >. e. S
                      )
                    )
              /\
              A. V e. ( ( 1st ` M ) ^m NN0 )
                A. i e. NN0
                  A. p e. ( Q1068283Formulas L )
                    (
                      <. V , <. 4 , <. i , p >. >. >. e. S
                      <->
                      A. x e. ( 1st ` M )
                        <.
                          (
                            j e. NN0
                            |->
                            if ( j = i , x , ( V ` j ) )
                          ) ,
                          p
                        >. e. S
                    )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d E F H L M N S T V p $.

  q1068283-elementary-embedding-definition $a |- (
    ( Q1068283ElemEmb L M N H )
    <->
    (
      (
        ( Q1068283Structure L M )
        /\
        ( Q1068283Structure L N )
      )
      /\
      (
        H : ( 1st ` M ) -1-1-> ( 1st ` N )
        /\
        E. E E. S E. F E. T
          (
            (
              ( Q1068283Eval L M E )
              /\
              ( Q1068283Sat L M E S )
            )
            /\
            (
              (
                ( Q1068283Eval L N F )
                /\
                ( Q1068283Sat L N F T )
              )
              /\
              A. V e. ( ( 1st ` M ) ^m NN0 )
                A. p e. ( Q1068283Formulas L )
                  (
                    <. V , p >. e. S
                    <->
                    <. ( H o. V ) , p >. e. T
                  )
            )
          )
      )
    )
  ) $.
$}

${
  $d H K L M N $.

  thousand-theorems-q1068283-lowenheim-skolem $a |- (
    A. L A. M A. K
      (
        (
          (
            ( Q1068283Language L )
            /\
            ( Q1068283Structure L M )
          )
          /\
          (
            _om ~<_ ( 1st ` M )
            /\
            (
              (
                ( card ` K ) = K
                /\
                _om ~<_ K
              )
              /\
              ( Q1068283Symbols L ) ~<_ K
            )
          )
        )
        ->
        E. N
          (
            ( Q1068283Structure L N )
            /\
            (
              (
                E. H ( Q1068283ElemEmb L N M H )
                \/
                E. H ( Q1068283ElemEmb L M N H )
              )
              /\
              ( card ` ( 1st ` N ) ) = K
            )
          )
      )
  ) $.
$}
