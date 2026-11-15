$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1893717
  (thousand-theorems__metamath__Q1893717), "Rice's theorem": every
  computably decidable property of partial-recursive program behavior that
  holds of one partial-recursive natural partial function holds of every such
  function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Nat.Partrec.Code is represented through its canonical bijection with NN0.
  Under this bijection the constructors have codes 0, 1, 2, 3,
  4*pair(c,d)+4, 4*pair(c,d)+6, 4*pair(c,d)+5, and 4*c+7. Q1893717Pair is
  Mathlib's exact Nat.pair function.

  Q1893717Eval c n y is the least relation closed under the operational rules
  for zero, successor, projections, pairing, composition, primitive
  recursion, and minimization. Thus it says that eval c n terminates with y.

  Q1893717Graph c is the graph of the partial function evaluated by c.
  Q1893717PFun is the full set of partial functions from NN0 to NN0, encoded
  as single-valued relations. Q1893717Partrec f says that f is the graph of
  some program code. Q1893717ComputablePred C says that membership of an
  evaluated graph in C is decided by a total program with Boolean outputs,
  where false and true are represented by 0 and 1.

  The final declaration preserves the arbitrary set C and the internal
  program witnesses for partial recursiveness and decidability. All auxiliary
  $a declarations are syntax or faithful definitions; the final $a is the
  single unproved corpus statement, and this database has no $p declaration.
$)

$c Q1893717Pair Q1893717CodePair Q1893717CodeComp $.
$c Q1893717CodePrec Q1893717CodeRfind $.
$c Q1893717Eval Q1893717Graph Q1893717PFun $.
$c Q1893717Partrec Q1893717ComputablePred $.

q1893717-pair-syntax $a class ( Q1893717Pair a b ) $.
q1893717-code-pair-syntax $a class ( Q1893717CodePair a b ) $.
q1893717-code-comp-syntax $a class ( Q1893717CodeComp a b ) $.
q1893717-code-prec-syntax $a class ( Q1893717CodePrec a b ) $.
q1893717-code-rfind-syntax $a class ( Q1893717CodeRfind a ) $.
q1893717-eval-syntax $a wff ( Q1893717Eval c n y ) $.
q1893717-graph-syntax $a class ( Q1893717Graph c ) $.
q1893717-partial-functions-syntax $a class Q1893717PFun $.
q1893717-partrec-syntax $a wff ( Q1893717Partrec f ) $.
q1893717-computable-predicate-syntax
  $a wff ( Q1893717ComputablePred C ) $.

q1893717-pair-definition $a |- (
  Q1893717Pair a b
  =
  if (
    a < b ,
    ( ( b x. b ) + a ) ,
    ( ( ( a x. a ) + a ) + b )
  )
) $.

q1893717-code-pair-definition $a |- (
  Q1893717CodePair a b
  =
  ( ( 4 x. ( Q1893717Pair a b ) ) + 4 )
) $.

q1893717-code-comp-definition $a |- (
  Q1893717CodeComp a b
  =
  ( ( 4 x. ( Q1893717Pair a b ) ) + 6 )
) $.

q1893717-code-prec-definition $a |- (
  Q1893717CodePrec a b
  =
  ( ( 4 x. ( Q1893717Pair a b ) ) + 5 )
) $.

q1893717-code-rfind-definition $a |- (
  Q1893717CodeRfind a
  =
  ( ( 4 x. a ) + 7 )
) $.

${
  $d R a b c i j k m n u v x y $.

  q1893717-eval-definition $a |- (
    ( Q1893717Eval c n y )
    <->
    A. R
      (
        (
          A. x e. NN0
            <. 0 , <. x , 0 >. >. e. R
          /\
          (
            A. x e. NN0
              <. 1 , <. x , ( x + 1 ) >. >. e. R
            /\
            (
              A. a e. NN0
                A. b e. NN0
                  <.
                    2 ,
                    <. ( Q1893717Pair a b ) , a >.
                  >. e. R
              /\
              (
                A. a e. NN0
                  A. b e. NN0
                    <.
                      3 ,
                      <. ( Q1893717Pair a b ) , b >.
                    >. e. R
                /\
                (
                  A. a e. NN0
                    A. b e. NN0
                      A. x e. NN0
                        A. u e. NN0
                          A. v e. NN0
                            (
                              (
                                <. a , <. x , u >. >. e. R
                                /\
                                <. b , <. x , v >. >. e. R
                              )
                              ->
                              <.
                                ( Q1893717CodePair a b ) ,
                                <. x , ( Q1893717Pair u v ) >.
                              >. e. R
                            )
                  /\
                  (
                    A. a e. NN0
                      A. b e. NN0
                        A. x e. NN0
                          A. u e. NN0
                            A. v e. NN0
                              (
                                (
                                  <. b , <. x , u >. >. e. R
                                  /\
                                  <. a , <. u , v >. >. e. R
                                )
                                ->
                                <.
                                  ( Q1893717CodeComp a b ) ,
                                  <. x , v >.
                                >. e. R
                              )
                    /\
                    (
                      A. a e. NN0
                        A. b e. NN0
                          A. x e. NN0
                            A. v e. NN0
                              (
                                <. a , <. x , v >. >. e. R
                                ->
                                <.
                                  ( Q1893717CodePrec a b ) ,
                                  <. ( Q1893717Pair x 0 ) , v >.
                                >. e. R
                              )
                      /\
                      (
                        A. a e. NN0
                          A. b e. NN0
                            A. x e. NN0
                              A. k e. NN0
                                A. u e. NN0
                                  A. v e. NN0
                                    (
                                      (
                                        <.
                                          ( Q1893717CodePrec a b ) ,
                                          <.
                                            ( Q1893717Pair x k ) ,
                                            u
                                          >.
                                        >. e. R
                                        /\
                                        <.
                                          b ,
                                          <.
                                            (
                                              Q1893717Pair
                                                x
                                                ( Q1893717Pair k u )
                                            ) ,
                                            v
                                          >.
                                        >. e. R
                                      )
                                      ->
                                      <.
                                        ( Q1893717CodePrec a b ) ,
                                        <.
                                          ( Q1893717Pair x ( k + 1 ) ) ,
                                          v
                                        >.
                                      >. e. R
                                    )
                        /\
                        A. a e. NN0
                          A. x e. NN0
                            A. m e. NN0
                              A. j e. NN0
                                (
                                  (
                                    <.
                                      a ,
                                      <.
                                        (
                                          Q1893717Pair
                                            x
                                            ( m + j )
                                        ) ,
                                        0
                                      >.
                                    >. e. R
                                    /\
                                    A. i e. ( 0 ..^ j )
                                      E. u e. NN0
                                        (
                                          u =/= 0
                                          /\
                                          <.
                                            a ,
                                            <.
                                              (
                                                Q1893717Pair
                                                  x
                                                  ( m + i )
                                              ) ,
                                              u
                                            >.
                                          >. e. R
                                        )
                                  )
                                  ->
                                  <.
                                    ( Q1893717CodeRfind a ) ,
                                    <.
                                      ( Q1893717Pair x m ) ,
                                      ( m + j )
                                    >.
                                  >. e. R
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
        <. c , <. n , y >. >. e. R
      )
  ) $.
$}

${
  $d c n r y $.

  q1893717-graph-definition $a |- (
    ( Q1893717Graph c )
    =
    { r e. ( NN0 X. NN0 ) |
      E. n e. NN0
        E. y e. NN0
          (
            r = <. n , y >.
            /\
            ( Q1893717Eval c n y )
          )
    }
  ) $.
$}

${
  $d f n y z $.

  q1893717-partial-functions-definition $a |- (
    Q1893717PFun
    =
    { f e. ~P ( NN0 X. NN0 ) |
      A. n e. NN0
        A. y e. NN0
          A. z e. NN0
            (
              (
                <. n , y >. e. f
                /\
                <. n , z >. e. f
              )
              ->
              y = z
            )
    }
  ) $.
$}

${
  $d c f $.

  q1893717-partrec-definition $a |- (
    ( Q1893717Partrec f )
    <->
    (
      f e. Q1893717PFun
      /\
      E. c e. NN0 f = ( Q1893717Graph c )
    )
  ) $.
$}

${
  $d C b c p $.

  q1893717-computable-predicate-definition $a |- (
    ( Q1893717ComputablePred C )
    <->
    (
      C e. ~P Q1893717PFun
      /\
      E. p e. NN0
        A. c e. NN0
          E. b e. { 0 , 1 }
            (
              ( Q1893717Eval p c b )
              /\
              (
                ( Q1893717Graph c ) e. C
                <->
                b = 1
              )
            )
    )
  ) $.
$}

${
  $d C f g $.

  thousand-theorems-q1893717-rice $a |- (
    A. C e. ~P Q1893717PFun
      A. f e. Q1893717PFun
        A. g e. Q1893717PFun
          (
            (
              ( Q1893717ComputablePred C )
              /\
              (
                ( Q1893717Partrec f )
                /\
                (
                  ( Q1893717Partrec g )
                  /\
                  f e. C
                )
              )
            )
            ->
            g e. C
          )
  ) $.
$}
