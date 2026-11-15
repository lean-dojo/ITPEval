$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1933521
  (thousand-theorems__metamath__Q1933521), "Kleene's recursion theorem":
  every binary partial-recursive natural-number computation has a program
  code whose evaluation is that computation specialized at its own code.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Nat.Partrec.Code is represented through its canonical bijection with NN0.
  Under this bijection the constructors have codes 0, 1, 2, 3,
  4*pair(c,d)+4, 4*pair(c,d)+6, 4*pair(c,d)+5, and 4*c+7. Q1933521Pair is
  Mathlib's exact Nat.pair function.

  Q1933521Eval c n y is the least relation closed under the operational rules
  for zero, successor, projections, pairing, composition, primitive
  recursion, and minimization. Thus it says that eval c n terminates with y.

  Q1933521Graph2 p is the graph of the binary partial function computed by p
  on paired inputs. Q1933521Partrec2 f says that f is exactly such a graph.
  The final pointwise biconditional over outputs is exactly equality of the
  partial values eval c and f c in the Lean statement. All auxiliary $a
  declarations are syntax or faithful definitions; the final $a is the
  single unproved corpus statement. This root artifact has no $p declaration;
  the included lib/set.mm supplies proved declarations.
$)

$c Q1933521Pair Q1933521CodePair Q1933521CodeComp $.
$c Q1933521CodePrec Q1933521CodeRfind $.
$c Q1933521Eval Q1933521Graph2 Q1933521Partrec2 $.

q1933521-pair-syntax $a class ( Q1933521Pair a b ) $.
q1933521-code-pair-syntax $a class ( Q1933521CodePair a b ) $.
q1933521-code-comp-syntax $a class ( Q1933521CodeComp a b ) $.
q1933521-code-prec-syntax $a class ( Q1933521CodePrec a b ) $.
q1933521-code-rfind-syntax $a class ( Q1933521CodeRfind a ) $.
q1933521-eval-syntax $a wff ( Q1933521Eval c n y ) $.
q1933521-graph2-syntax $a class ( Q1933521Graph2 p ) $.
q1933521-partrec2-syntax $a wff ( Q1933521Partrec2 f ) $.

q1933521-pair-definition $a |- (
  Q1933521Pair a b
  =
  if (
    a < b ,
    ( ( b x. b ) + a ) ,
    ( ( ( a x. a ) + a ) + b )
  )
) $.

q1933521-code-pair-definition $a |- (
  Q1933521CodePair a b
  =
  ( ( 4 x. ( Q1933521Pair a b ) ) + 4 )
) $.

q1933521-code-comp-definition $a |- (
  Q1933521CodeComp a b
  =
  ( ( 4 x. ( Q1933521Pair a b ) ) + 6 )
) $.

q1933521-code-prec-definition $a |- (
  Q1933521CodePrec a b
  =
  ( ( 4 x. ( Q1933521Pair a b ) ) + 5 )
) $.

q1933521-code-rfind-definition $a |- (
  Q1933521CodeRfind a
  =
  ( ( 4 x. a ) + 7 )
) $.

${
  $d R a b c i j k m n u v x y $.

  q1933521-eval-definition $a |- (
    ( Q1933521Eval c n y )
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
                    <. ( Q1933521Pair a b ) , a >.
                  >. e. R
              /\
              (
                A. a e. NN0
                  A. b e. NN0
                    <.
                      3 ,
                      <. ( Q1933521Pair a b ) , b >.
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
                                ( Q1933521CodePair a b ) ,
                                <. x , ( Q1933521Pair u v ) >.
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
                                  ( Q1933521CodeComp a b ) ,
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
                                  ( Q1933521CodePrec a b ) ,
                                  <. ( Q1933521Pair x 0 ) , v >.
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
                                          ( Q1933521CodePrec a b ) ,
                                          <.
                                            ( Q1933521Pair x k ) ,
                                            u
                                          >.
                                        >. e. R
                                        /\
                                        <.
                                          b ,
                                          <.
                                            (
                                              Q1933521Pair
                                                x
                                                ( Q1933521Pair k u )
                                            ) ,
                                            v
                                          >.
                                        >. e. R
                                      )
                                      ->
                                      <.
                                        ( Q1933521CodePrec a b ) ,
                                        <.
                                          ( Q1933521Pair x ( k + 1 ) ) ,
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
                                          Q1933521Pair
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
                                                Q1933521Pair
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
                                    ( Q1933521CodeRfind a ) ,
                                    <.
                                      ( Q1933521Pair x m ) ,
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
  $d c f n p r y $.

  q1933521-graph2-definition $a |- (
    ( Q1933521Graph2 p )
    =
    { r e. ( NN0 X. ( NN0 X. NN0 ) ) |
      E. c e. NN0
        E. n e. NN0
          E. y e. NN0
            (
              r = <. c , <. n , y >. >.
              /\
              (
                Q1933521Eval
                  p
                  ( Q1933521Pair c n )
                  y
              )
            )
    }
  ) $.

  q1933521-partrec2-definition $a |- (
    ( Q1933521Partrec2 f )
    <->
    (
      f e. ~P ( NN0 X. ( NN0 X. NN0 ) )
      /\
      E. p e. NN0
        f = ( Q1933521Graph2 p )
    )
  ) $.
$}

${
  $d c f n y $.

  thousand-theorems-q1933521-kleene-recursion $a |- (
    A. f e. ~P ( NN0 X. ( NN0 X. NN0 ) )
      (
        ( Q1933521Partrec2 f )
        ->
        E. c e. NN0
          A. n e. NN0
            A. y e. NN0
              (
                ( Q1933521Eval c n y )
                <->
                <. c , <. n , y >. >. e. f
              )
      )
  ) $.
$}
