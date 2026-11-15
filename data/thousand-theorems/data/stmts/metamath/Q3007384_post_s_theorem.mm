$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3007384
  (thousand-theorems__metamath__Q3007384), "Post's theorem": on every
  Primcodable domain, a predicate is computable exactly when both it and its
  complement are recursively enumerable. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Nat.Partrec.Code is represented through its canonical bijection with NN0.
  Under this bijection the constructors have codes 0, 1, 2, 3,
  4*pair(c,d)+4, 4*pair(c,d)+6, 4*pair(c,d)+5, and 4*c+7. Q3007384Pair is
  Mathlib's exact Nat.pair function. Q3007384Eval c n y is the least relation
  closed under the operational rules for zero, successor, projections,
  pairing, composition, primitive recursion, and minimization, so it says
  that program c on input n terminates with output y.

  Q3007384PrimrecCodes is the least set of codes generated without
  minimization. Q3007384PrimcodableCarrier S says that S is a subset of NN0
  and the function sending n to n+1 on S and to 0 off S has a
  primitive-recursive code. This is exactly the Primcodable condition on the
  image S of Encodable.encode, since that function is
  encode(decode(n)) for the Option encoding. Conversely, every such S,
  regarded as a subtype of NN0, has the corresponding Primcodable instance.
  Thus quantifying over these carriers is bidirectionally equivalent to
  quantifying over arbitrary source Primcodable types, not a restriction to
  the natural-number type.

  Q3007384ComputablePred S P requires one program whose exact graph returns
  Boolean code 1 on P, Boolean code 0 on S \ P, and diverges outside S.
  Q3007384REPred S P requires one program whose exact graph returns the unit
  code 0 precisely on P. These are the encoded graphs in the source
  definitions of ComputablePred and REPred. SetMM is classical, so the
  source's external DecidablePred parameter adds no restriction and does not
  alter either side of the equivalence.

  Every auxiliary $a declaration is syntax or a faithful definition. The
  final $a declaration is the single unproved corpus statement, and this
  database contains no $p declaration.
$)

$c Q3007384Pair Q3007384CodePair Q3007384CodeComp $.
$c Q3007384CodePrec Q3007384CodeRfind $.
$c Q3007384Eval Q3007384PrimrecCodes $.
$c Q3007384PrimcodableCarrier Q3007384ComputablePred Q3007384REPred $.

q3007384-pair-syntax $a class ( Q3007384Pair a b ) $.
q3007384-code-pair-syntax $a class ( Q3007384CodePair a b ) $.
q3007384-code-comp-syntax $a class ( Q3007384CodeComp a b ) $.
q3007384-code-prec-syntax $a class ( Q3007384CodePrec a b ) $.
q3007384-code-rfind-syntax $a class ( Q3007384CodeRfind a ) $.
q3007384-eval-syntax $a wff ( Q3007384Eval c n y ) $.
q3007384-primrec-codes-syntax $a class Q3007384PrimrecCodes $.
q3007384-primcodable-carrier-syntax
  $a wff ( Q3007384PrimcodableCarrier S ) $.
q3007384-computable-predicate-syntax
  $a wff ( Q3007384ComputablePred S P ) $.
q3007384-re-predicate-syntax
  $a wff ( Q3007384REPred S P ) $.

q3007384-pair-definition $a |- (
  Q3007384Pair a b
  =
  if (
    a < b ,
    ( ( b x. b ) + a ) ,
    ( ( ( a x. a ) + a ) + b )
  )
) $.

q3007384-code-pair-definition $a |- (
  Q3007384CodePair a b
  =
  ( ( 4 x. ( Q3007384Pair a b ) ) + 4 )
) $.

q3007384-code-comp-definition $a |- (
  Q3007384CodeComp a b
  =
  ( ( 4 x. ( Q3007384Pair a b ) ) + 6 )
) $.

q3007384-code-prec-definition $a |- (
  Q3007384CodePrec a b
  =
  ( ( 4 x. ( Q3007384Pair a b ) ) + 5 )
) $.

q3007384-code-rfind-definition $a |- (
  Q3007384CodeRfind a
  =
  ( ( 4 x. a ) + 7 )
) $.

${
  $d R a b c i j k m n u v x y $.

  q3007384-eval-definition $a |- (
    ( Q3007384Eval c n y )
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
                    <. ( Q3007384Pair a b ) , a >.
                  >. e. R
              /\
              (
                A. a e. NN0
                  A. b e. NN0
                    <.
                      3 ,
                      <. ( Q3007384Pair a b ) , b >.
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
                                ( Q3007384CodePair a b ) ,
                                <. x , ( Q3007384Pair u v ) >.
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
                                  ( Q3007384CodeComp a b ) ,
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
                                  ( Q3007384CodePrec a b ) ,
                                  <. ( Q3007384Pair x 0 ) , v >.
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
                                          ( Q3007384CodePrec a b ) ,
                                          <.
                                            ( Q3007384Pair x k ) ,
                                            u
                                          >.
                                        >. e. R
                                        /\
                                        <.
                                          b ,
                                          <.
                                            (
                                              Q3007384Pair
                                                x
                                                ( Q3007384Pair k u )
                                            ) ,
                                            v
                                          >.
                                        >. e. R
                                      )
                                      ->
                                      <.
                                        ( Q3007384CodePrec a b ) ,
                                        <.
                                          ( Q3007384Pair x ( k + 1 ) ) ,
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
                                          Q3007384Pair
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
                                                Q3007384Pair
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
                                    ( Q3007384CodeRfind a ) ,
                                    <.
                                      ( Q3007384Pair x m ) ,
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
  $d C a b $.

  q3007384-primrec-codes-definition $a |-
    Q3007384PrimrecCodes
    =
    |^| { C |
      (
        (
          0 e. C
          /\
          1 e. C
        )
        /\
        (
          (
            2 e. C
            /\
            3 e. C
          )
          /\
          A. a e. C
            A. b e. C
              (
                ( Q3007384CodePair a b ) e. C
                /\
                (
                  ( Q3007384CodeComp a b ) e. C
                  /\
                  ( Q3007384CodePrec a b ) e. C
                )
              )
        )
      )
    } $.
$}

${
  $d S d n $.

  q3007384-primcodable-carrier-definition $a |- (
    ( Q3007384PrimcodableCarrier S )
    <->
    (
      S e. ~P NN0
      /\
      E. d e. Q3007384PrimrecCodes
        A. n e. NN0
          (
            Q3007384Eval
              d
              n
              if (
                n e. S ,
                ( n + 1 ) ,
                0
              )
          )
    )
  ) $.
$}

${
  $d P S c n y $.

  q3007384-computable-predicate-definition $a |- (
    ( Q3007384ComputablePred S P )
    <->
    (
      P e. ~P S
      /\
      E. c e. NN0
        A. n e. NN0
          A. y e. NN0
            (
              ( Q3007384Eval c n y )
              <->
              (
                (
                  n e. P
                  /\
                  y = 1
                )
                \/
                (
                  n e. ( S \ P )
                  /\
                  y = 0
                )
              )
            )
    )
  ) $.

  q3007384-re-predicate-definition $a |- (
    ( Q3007384REPred S P )
    <->
    (
      P e. ~P S
      /\
      E. c e. NN0
        A. n e. NN0
          A. y e. NN0
            (
              ( Q3007384Eval c n y )
              <->
              (
                n e. P
                /\
                y = 0
              )
            )
    )
  ) $.
$}

${
  $d P S $.

  thousand-theorems-q3007384-post $a |- (
    A. S e. ~P NN0
      A. P e. ~P S
        (
          ( Q3007384PrimcodableCarrier S )
          ->
          (
            ( Q3007384ComputablePred S P )
            <->
            (
              ( Q3007384REPred S P )
              /\
              ( Q3007384REPred S ( S \ P ) )
            )
          )
        )
  ) $.
$}
