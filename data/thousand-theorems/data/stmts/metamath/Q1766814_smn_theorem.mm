$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1766814
  (thousand-theorems__metamath__Q1766814), "Smn theorem": there is a
  computable operation specializing a partial-recursive program code at its
  first natural-number argument while preserving its partial evaluation.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Nat.Partrec.Code is represented through its canonical bijection with NN0.
  Under this bijection the constructors have codes 0, 1, 2, 3,
  4*pair(c,d)+4, 4*pair(c,d)+6, 4*pair(c,d)+5, and 4*c+7. Q1766814Pair is
  Mathlib's exact Nat.pair function.

  Q1766814Eval c n y is the least relation closed under the operational rules
  for zero, successor, projections, pairing, composition, primitive
  recursion, and minimization. Thus it says that eval c n terminates with y.
  Q1766814Computable2 F says that the total binary function F on code-naturals
  is realized by one program code on paired inputs.

  The final pointwise biconditional over possible outputs is exactly equality
  of the two partial values in the Lean statement. All auxiliary $a
  declarations are syntax or faithful definitions; the final $a is the
  single unproved corpus statement, and this database has no $p declaration.
$)

$c Q1766814Pair Q1766814CodePair Q1766814CodeComp $.
$c Q1766814CodePrec Q1766814CodeRfind $.
$c Q1766814Eval Q1766814Computable2 $.

q1766814-pair-syntax $a class ( Q1766814Pair a b ) $.
q1766814-code-pair-syntax $a class ( Q1766814CodePair a b ) $.
q1766814-code-comp-syntax $a class ( Q1766814CodeComp a b ) $.
q1766814-code-prec-syntax $a class ( Q1766814CodePrec a b ) $.
q1766814-code-rfind-syntax $a class ( Q1766814CodeRfind a ) $.
q1766814-eval-syntax $a wff ( Q1766814Eval c n y ) $.
q1766814-computable2-syntax $a wff ( Q1766814Computable2 F ) $.

q1766814-pair-definition $a |- (
  Q1766814Pair a b
  =
  if (
    a < b ,
    ( ( b x. b ) + a ) ,
    ( ( ( a x. a ) + a ) + b )
  )
) $.

q1766814-code-pair-definition $a |- (
  Q1766814CodePair a b
  =
  ( ( 4 x. ( Q1766814Pair a b ) ) + 4 )
) $.

q1766814-code-comp-definition $a |- (
  Q1766814CodeComp a b
  =
  ( ( 4 x. ( Q1766814Pair a b ) ) + 6 )
) $.

q1766814-code-prec-definition $a |- (
  Q1766814CodePrec a b
  =
  ( ( 4 x. ( Q1766814Pair a b ) ) + 5 )
) $.

q1766814-code-rfind-definition $a |- (
  Q1766814CodeRfind a
  =
  ( ( 4 x. a ) + 7 )
) $.

${
  $d R a b c i j k m n u v x y $.

  q1766814-eval-definition $a |- (
    ( Q1766814Eval c n y )
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
                    <. ( Q1766814Pair a b ) , a >.
                  >. e. R
              /\
              (
                A. a e. NN0
                  A. b e. NN0
                    <.
                      3 ,
                      <. ( Q1766814Pair a b ) , b >.
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
                                ( Q1766814CodePair a b ) ,
                                <. x , ( Q1766814Pair u v ) >.
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
                                  ( Q1766814CodeComp a b ) ,
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
                                  ( Q1766814CodePrec a b ) ,
                                  <. ( Q1766814Pair x 0 ) , v >.
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
                                          ( Q1766814CodePrec a b ) ,
                                          <.
                                            ( Q1766814Pair x k ) ,
                                            u
                                          >.
                                        >. e. R
                                        /\
                                        <.
                                          b ,
                                          <.
                                            (
                                              Q1766814Pair
                                                x
                                                ( Q1766814Pair k u )
                                            ) ,
                                            v
                                          >.
                                        >. e. R
                                      )
                                      ->
                                      <.
                                        ( Q1766814CodePrec a b ) ,
                                        <.
                                          ( Q1766814Pair x ( k + 1 ) ) ,
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
                                          Q1766814Pair
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
                                                Q1766814Pair
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
                                    ( Q1766814CodeRfind a ) ,
                                    <.
                                      ( Q1766814Pair x m ) ,
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
  $d F c n p $.

  q1766814-computable2-definition $a |- (
    ( Q1766814Computable2 F )
    <->
    (
      F : ( NN0 X. NN0 ) --> NN0
      /\
      E. p e. NN0
        A. c e. NN0
          A. n e. NN0
            (
              Q1766814Eval
                p
                ( Q1766814Pair c n )
                ( F ` <. c , n >. )
            )
    )
  ) $.
$}

${
  $d F c n x y $.

  thousand-theorems-q1766814-smn $a |- (
    E. F
      (
        ( Q1766814Computable2 F )
        /\
        A. c e. NN0
          A. n e. NN0
            A. x e. NN0
              A. y e. NN0
                (
                  (
                    Q1766814Eval
                      ( F ` <. c , n >. )
                      x
                      y
                  )
                  <->
                  (
                    Q1766814Eval
                      c
                      ( Q1766814Pair n x )
                      y
                  )
                )
      )
  ) $.
$}
