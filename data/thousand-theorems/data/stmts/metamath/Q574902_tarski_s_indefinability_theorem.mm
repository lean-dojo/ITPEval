$(
  Statement-only formalization of Thousand Theorems corpus artifact Q574902
  (thousand-theorems__metamath__Q574902), "Tarski's indefinability theorem":
  no arithmetic formula with at most one free variable defines, by
  substitution of sentence codes, truth of every arithmetic sentence in the
  standard natural-number model. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Arithmetic terms and formulas are concrete finite tagged trees for the
  ordered-semiring language with zero, one, addition, multiplication, and
  strict order. Q574902TermsAt n contains the terms whose de Bruijn variable
  indices are below n. Q574902FormulaLevels contains <. n , p >. exactly when
  p is a formula with n available variables; universal quantification binds
  the last available variable. Thus level zero gives sentences and level one
  gives semisentences with at most one free variable.

  Q574902Eval and Q574902Sat are the compositional Tarski semantics in the
  standard model NN0. Q574902CodeFormula is an explicit Goedel coding, and
  Q574902Instantiate replaces variable zero by the closed numeral for a code,
  shifting the remaining de Bruijn indices down by one.

  Foundation uses truth, falsity, positive and negative atoms, conjunction,
  disjunction, universal quantification, and existential quantification as
  primitive formula constructors. Its basis and the positive-atom,
  implication, negation, and universal-quantification basis used here are
  recursively intertranslatable in both directions while preserving
  standard-model satisfaction; the omitted connectives have their usual
  classical definitions. Likewise, this injective Goedel numbering and
  Foundation's constructor numbering are recursively interconvertible on
  well-formed terms and formulas. Arithmetic represents both recoding maps,
  so a unary arithmetic truth definition relative to either presentation
  transports to one relative to the other, in both directions.

  The final unproved $a assertion is therefore bidirectionally logically
  equivalent to the cataloged negation of the existence of a unary arithmetic
  truth predicate, rather than a restriction to weaker syntax or externally
  supplied witnesses. All earlier $a declarations are syntax or faithful
  definitions, and this database contains no $p statement.
$)

$c Q574902Var Q574902Zero Q574902One Q574902Add Q574902Mul $.
$c Q574902Eq Q574902Lt Q574902Imp Q574902Neg Q574902All $.
$c Q574902TermsAt Q574902Terms Q574902FormulaLevels $.
$c Q574902Formulas Q574902Sentences Q574902UnaryFormulas $.
$c Q574902PairCode Q574902CodeTerm Q574902CodeFormula $.
$c Q574902Numeral Q574902InstTerm Q574902Instantiate $.
$c Q574902Eval Q574902Sat Q574902Truth $.

q574902-var-syntax $a class ( Q574902Var A ) $.
q574902-zero-syntax $a class Q574902Zero $.
q574902-one-syntax $a class Q574902One $.
q574902-add-syntax $a class ( Q574902Add A B ) $.
q574902-mul-syntax $a class ( Q574902Mul A B ) $.
q574902-eq-syntax $a class ( Q574902Eq A B ) $.
q574902-lt-syntax $a class ( Q574902Lt A B ) $.
q574902-imp-syntax $a class ( Q574902Imp A B ) $.
q574902-neg-syntax $a class ( Q574902Neg A ) $.
q574902-all-syntax $a class ( Q574902All A ) $.
q574902-terms-at-syntax $a class ( Q574902TermsAt A ) $.
q574902-terms-syntax $a class Q574902Terms $.
q574902-formula-levels-syntax $a class Q574902FormulaLevels $.
q574902-formulas-syntax $a class Q574902Formulas $.
q574902-sentences-syntax $a class Q574902Sentences $.
q574902-unary-formulas-syntax $a class Q574902UnaryFormulas $.
q574902-pair-code-syntax $a class ( Q574902PairCode A B ) $.
q574902-code-term-syntax $a class ( Q574902CodeTerm A ) $.
q574902-code-formula-syntax $a class ( Q574902CodeFormula A ) $.
q574902-numeral-syntax $a class ( Q574902Numeral A ) $.
q574902-inst-term-syntax $a class ( Q574902InstTerm A B ) $.
q574902-instantiate-syntax $a class ( Q574902Instantiate A B ) $.
q574902-eval-syntax $a wff ( Q574902Eval E ) $.
q574902-sat-syntax $a wff ( Q574902Sat E S ) $.
q574902-truth-syntax $a wff ( Q574902Truth A ) $.

q574902-var-definition $a |- ( Q574902Var A ) = <. 0 , A >. $.
q574902-zero-definition $a |- Q574902Zero = <. 1 , 0 >. $.
q574902-one-definition $a |- Q574902One = <. 2 , 0 >. $.
q574902-add-definition $a |- ( Q574902Add A B ) =
  <. 3 , <. A , B >. >. $.
q574902-mul-definition $a |- ( Q574902Mul A B ) =
  <. 4 , <. A , B >. >. $.
q574902-eq-definition $a |- ( Q574902Eq A B ) =
  <. 5 , <. A , B >. >. $.
q574902-lt-definition $a |- ( Q574902Lt A B ) =
  <. 6 , <. A , B >. >. $.
q574902-imp-definition $a |- ( Q574902Imp A B ) =
  <. 7 , <. A , B >. >. $.
q574902-neg-definition $a |- ( Q574902Neg A ) = <. 8 , A >. $.
q574902-all-definition $a |- ( Q574902All A ) = <. 9 , A >. $.

${
  $d A B C i n $.

  q574902-terms-at-definition $a |- ( Q574902TermsAt n ) =
    |^| { C |
      (
        (
          A. i e. ( 0 ..^ n ) ( Q574902Var i ) e. C
          /\
          Q574902Zero e. C
        )
        /\
        (
          Q574902One e. C
          /\
          A. A e. C A. B e. C
            (
              ( Q574902Add A B ) e. C
              /\
              ( Q574902Mul A B ) e. C
            )
        )
      )
    } $.
$}

q574902-terms-definition $a |- Q574902Terms =
  U_ n e. NN0 ( Q574902TermsAt n ) $.

${
  $d A B C n $.

  q574902-formula-levels-definition $a |- Q574902FormulaLevels =
    |^| { C |
      A. n e. NN0
        (
          A. A e. ( Q574902TermsAt n )
            A. B e. ( Q574902TermsAt n )
              (
                <. n , ( Q574902Eq A B ) >. e. C
                /\
                <. n , ( Q574902Lt A B ) >. e. C
              )
          /\
          (
            A. A A. B
              (
                (
                  <. n , A >. e. C
                  /\
                  <. n , B >. e. C
                )
                ->
                <. n , ( Q574902Imp A B ) >. e. C
              )
            /\
            (
              A. A
                (
                  <. n , A >. e. C
                  ->
                  <. n , ( Q574902Neg A ) >. e. C
                )
              /\
              A. A
                (
                  <. ( n + 1 ) , A >. e. C
                  ->
                  <. n , ( Q574902All A ) >. e. C
                )
            )
          )
        )
    } $.
$}

q574902-formulas-definition $a |- Q574902Formulas =
  ran Q574902FormulaLevels $.

q574902-sentences-definition $a |- Q574902Sentences =
  { A e. Q574902Formulas | <. 0 , A >. e. Q574902FormulaLevels } $.

q574902-unary-formulas-definition $a |- Q574902UnaryFormulas =
  { A e. Q574902Formulas | <. 1 , A >. e. Q574902FormulaLevels } $.

q574902-pair-code-definition $a |- ( Q574902PairCode A B ) =
  ( ( 2 ^ A ) x. ( ( 2 x. B ) + 1 ) ) $.

q574902-code-term-var $a |- (
  Q574902CodeTerm ( Q574902Var A )
) = ( 5 x. A ) $.

q574902-code-term-zero $a |- (
  Q574902CodeTerm Q574902Zero
) = 1 $.

q574902-code-term-one $a |- (
  Q574902CodeTerm Q574902One
) = 2 $.

q574902-code-term-add $a |- (
  Q574902CodeTerm ( Q574902Add A B )
) = (
  ( 5 x.
    ( Q574902PairCode
      ( Q574902CodeTerm A )
      ( Q574902CodeTerm B ) ) )
  + 3
) $.

q574902-code-term-mul $a |- (
  Q574902CodeTerm ( Q574902Mul A B )
) = (
  ( 5 x.
    ( Q574902PairCode
      ( Q574902CodeTerm A )
      ( Q574902CodeTerm B ) ) )
  + 4
) $.

q574902-code-formula-eq $a |- (
  Q574902CodeFormula ( Q574902Eq A B )
) = (
  5 x.
  ( Q574902PairCode
    ( Q574902CodeTerm A )
    ( Q574902CodeTerm B ) )
) $.

q574902-code-formula-lt $a |- (
  Q574902CodeFormula ( Q574902Lt A B )
) = (
  ( 5 x.
    ( Q574902PairCode
      ( Q574902CodeTerm A )
      ( Q574902CodeTerm B ) ) )
  + 1
) $.

q574902-code-formula-imp $a |- (
  Q574902CodeFormula ( Q574902Imp A B )
) = (
  ( 5 x.
    ( Q574902PairCode
      ( Q574902CodeFormula A )
      ( Q574902CodeFormula B ) ) )
  + 2
) $.

q574902-code-formula-neg $a |- (
  Q574902CodeFormula ( Q574902Neg A )
) = ( ( 5 x. ( Q574902CodeFormula A ) ) + 3 ) $.

q574902-code-formula-all $a |- (
  Q574902CodeFormula ( Q574902All A )
) = ( ( 5 x. ( Q574902CodeFormula A ) ) + 4 ) $.

q574902-numeral-zero $a |- (
  Q574902Numeral 0
) = Q574902Zero $.

q574902-numeral-successor $a |- (
  A e. NN0
  ->
  ( Q574902Numeral ( A + 1 ) ) =
    ( Q574902Add ( Q574902Numeral A ) Q574902One )
) $.

q574902-inst-term-var $a |- (
  Q574902InstTerm ( Q574902Var A ) B
) = if (
  A = 0 ,
  ( Q574902Numeral B ) ,
  ( Q574902Var U. A )
) $.

q574902-inst-term-zero $a |- (
  Q574902InstTerm Q574902Zero B
) = Q574902Zero $.

q574902-inst-term-one $a |- (
  Q574902InstTerm Q574902One B
) = Q574902One $.

q574902-inst-term-add $a |- (
  Q574902InstTerm ( Q574902Add A B ) C
) = (
  Q574902Add
    ( Q574902InstTerm A C )
    ( Q574902InstTerm B C )
) $.

q574902-inst-term-mul $a |- (
  Q574902InstTerm ( Q574902Mul A B ) C
) = (
  Q574902Mul
    ( Q574902InstTerm A C )
    ( Q574902InstTerm B C )
) $.

q574902-instantiate-eq $a |- (
  Q574902Instantiate ( Q574902Eq A B ) C
) = (
  Q574902Eq
    ( Q574902InstTerm A C )
    ( Q574902InstTerm B C )
) $.

q574902-instantiate-lt $a |- (
  Q574902Instantiate ( Q574902Lt A B ) C
) = (
  Q574902Lt
    ( Q574902InstTerm A C )
    ( Q574902InstTerm B C )
) $.

q574902-instantiate-imp $a |- (
  Q574902Instantiate ( Q574902Imp A B ) C
) = (
  Q574902Imp
    ( Q574902Instantiate A C )
    ( Q574902Instantiate B C )
) $.

q574902-instantiate-neg $a |- (
  Q574902Instantiate ( Q574902Neg A ) C
) = ( Q574902Neg ( Q574902Instantiate A C ) ) $.

q574902-instantiate-all $a |- (
  Q574902Instantiate ( Q574902All A ) C
) = ( Q574902All ( Q574902Instantiate A C ) ) $.

${
  $d A B E V i $.

  q574902-eval-definition $a |- (
    ( Q574902Eval E )
    <->
    (
      E : ( ( NN0 ^m NN0 ) X. Q574902Terms ) --> NN0
      /\
      (
        A. V e. ( NN0 ^m NN0 ) A. i e. NN0
          ( E ` <. V , ( Q574902Var i ) >. ) = ( V ` i )
        /\
        (
          A. V e. ( NN0 ^m NN0 )
            (
              ( E ` <. V , Q574902Zero >. ) = 0
              /\
              ( E ` <. V , Q574902One >. ) = 1
            )
          /\
          A. V e. ( NN0 ^m NN0 )
            A. A e. Q574902Terms A. B e. Q574902Terms
              (
                (
                  E ` <. V , ( Q574902Add A B ) >.
                )
                =
                (
                  ( E ` <. V , A >. )
                  +
                  ( E ` <. V , B >. )
                )
                /\
                (
                  E ` <. V , ( Q574902Mul A B ) >.
                )
                =
                (
                  ( E ` <. V , A >. )
                  x.
                  ( E ` <. V , B >. )
                )
              )
        )
      )
    )
  ) $.
$}

${
  $d A B E S V i n x $.

  q574902-sat-definition $a |- (
    ( Q574902Sat E S )
    <->
    (
      S C_ ( ( NN0 ^m NN0 ) X. Q574902FormulaLevels )
      /\
      A. n e. NN0
        (
          A. V e. ( NN0 ^m NN0 )
            A. A e. ( Q574902TermsAt n )
              A. B e. ( Q574902TermsAt n )
                (
                  (
                    <. V , <. n , ( Q574902Eq A B ) >. >. e. S
                    <->
                    ( E ` <. V , A >. ) = ( E ` <. V , B >. )
                  )
                  /\
                  (
                    <. V , <. n , ( Q574902Lt A B ) >. >. e. S
                    <->
                    ( E ` <. V , A >. ) < ( E ` <. V , B >. )
                  )
                )
          /\
          (
            A. V e. ( NN0 ^m NN0 ) A. A A. B
              (
                (
                  <. n , A >. e. Q574902FormulaLevels
                  /\
                  <. n , B >. e. Q574902FormulaLevels
                )
                ->
                (
                  <. V , <. n , ( Q574902Imp A B ) >. >. e. S
                  <->
                  (
                    <. V , <. n , A >. >. e. S
                    ->
                    <. V , <. n , B >. >. e. S
                  )
                )
              )
            /\
            (
              A. V e. ( NN0 ^m NN0 ) A. A
                (
                  <. n , A >. e. Q574902FormulaLevels
                  ->
                  (
                    <. V , <. n , ( Q574902Neg A ) >. >. e. S
                    <->
                    -. <. V , <. n , A >. >. e. S
                  )
                )
              /\
              A. V e. ( NN0 ^m NN0 ) A. A
                (
                  <. ( n + 1 ) , A >. e. Q574902FormulaLevels
                  ->
                  (
                    <. V , <. n , ( Q574902All A ) >. >. e. S
                    <->
                    A. x e. NN0
                      <.
                        (
                          i e. NN0
                          |->
                          if ( i = n , x , ( V ` i ) )
                        ) ,
                        <. ( n + 1 ) , A >.
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
  $d A E S V $.

  q574902-truth-definition $a |- (
    ( Q574902Truth A )
    <->
    (
      A e. Q574902Sentences
      /\
      E. E E. S
        (
          (
            ( Q574902Eval E )
            /\
            ( Q574902Sat E S )
          )
          /\
          A. V e. ( NN0 ^m NN0 )
            <. V , <. 0 , A >. >. e. S
        )
    )
  ) $.
$}

${
  $d p t $.

  thousand-theorems-q574902-tarski-indefinability $a |- (
    -. E. t
      (
        t e. Q574902UnaryFormulas
        /\
        A. p e. Q574902Sentences
          (
            ( Q574902Truth p )
            <->
            (
              Q574902Truth
                ( Q574902Instantiate t ( Q574902CodeFormula p ) )
            )
          )
      )
  ) $.
$}
