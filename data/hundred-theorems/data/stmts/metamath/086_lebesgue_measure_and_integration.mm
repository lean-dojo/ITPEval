$(
  Statement-only formalization of Hundred Theorems artifact 086, "Lebesgue
  Measure and Integration". It states existence and uniqueness on measurable
  functions of the lower Lebesgue integral over every measure space, together
  with indicator normalization, monotonicity, additivity, almost-everywhere
  congruence, and monotone convergence. This file contains no proof.
$)

$[ library/set.mm $]

$(
  Measures and their sigma-algebras use the native set.mm representation:
  M e. U. ran measures, with measurable sets dom M and sample space
  U. dom M. Extended nonnegative values use the set.mm class
  ( 0 [,] +oo ), and +e and *e are the extended-real operations.

  HT086Measurable uses inverse images of finite lower rays, which generate the
  Borel sigma-algebra of ( 0 [,] +oo ). HT086AE is equality outside an
  internally quantified measurable null set. HT086PointwiseSup states that G
  is the pointwise supremum of a sequence H.

  HT086Laws characterizes a lower-integral functional on all
  ( 0 [,] +oo )-valued functions. The final assertion quantifies the integral
  witness internally and states uniqueness on measurable functions. Every
  declaration is an unproved $a statement; this database contains no $p proof
  statement.
$)

$c HT086Measurable HT086AE HT086Indicator HT086PointwiseSup HT086Laws $.

ht086-measurable-syntax $a wff ( HT086Measurable M F ) $.
ht086-ae-syntax $a wff ( HT086AE M F G ) $.
ht086-indicator-syntax $a class ( HT086Indicator M S F ) $.
ht086-pointwise-sup-syntax $a wff ( HT086PointwiseSup M H G ) $.
ht086-laws-syntax $a wff ( HT086Laws M I ) $.

${
  $d F M r x $.

  ht086-measurable-definition $a |- (
    ( HT086Measurable M F )
    <->
    (
      F : U. dom M --> ( 0 [,] +oo )
      /\
      A. r e. RR
        { x e. U. dom M | ( F ` x ) <_ r } e. dom M
    )
  ) $.
$}

${
  $d F G M N x $.

  ht086-ae-definition $a |- (
    ( HT086AE M F G )
    <->
    E. N e. dom M
      (
        ( M ` N ) = 0
        /\
        A. x e. ( U. dom M \ N ) ( F ` x ) = ( G ` x )
      )
  ) $.
$}

${
  $d F M S x $.

  ht086-indicator-definition $a |- (
    HT086Indicator M S F
    =
    ( x e. U. dom M |->
      if ( x e. S , ( F ` x ) , 0 ) )
  ) $.
$}

${
  $d G H M n x y $.

  ht086-pointwise-sup-definition $a |- (
    ( HT086PointwiseSup M H G )
    <->
    (
      H : NN0 --> ( ( 0 [,] +oo ) ^m U. dom M )
      /\
      (
        G : U. dom M --> ( 0 [,] +oo )
        /\
        A. x e. U. dom M
          ( G ` x )
          =
          sup
          (
            { y e. ( 0 [,] +oo ) |
              E. n e. NN0 y = ( ( H ` n ) ` x )
            } ,
            RR* ,
            <
          )
      )
    )
  ) $.
$}

${
  $d F G H I M N S c n x $.
  $d F G H I M S c n x $.
  $d F G H I M n x $.
  $d F G I M S c x $.
  $d F G I M x $.
  $d F I M N x $.
  $d F I M x $.
  $d I M S c x $.
  $d I M x $.

  ht086-laws-definition $a |- (
    ( HT086Laws M I )
    <->
    (
      I : ( ( 0 [,] +oo ) ^m U. dom M ) --> ( 0 [,] +oo )
      /\
      (
        ( I ` ( x e. U. dom M |-> 0 ) ) = 0
        /\
        (
          A. S e. dom M A. c e. ( 0 [,] +oo )
            ( I `
              ( HT086Indicator M S
                ( x e. U. dom M |-> c ) )
            )
            =
            ( c *e ( M ` S ) )
          /\
          (
            A. F A. G
              (
                (
                  F e. ( ( 0 [,] +oo ) ^m U. dom M )
                  /\
                  (
                    G e. ( ( 0 [,] +oo ) ^m U. dom M )
                    /\
                    A. x e. U. dom M
                      ( F ` x ) <_ ( G ` x )
                  )
                )
                ->
                ( I ` F ) <_ ( I ` G )
              )
            /\
            (
              A. F A. G
                (
                  (
                    ( HT086Measurable M F )
                    /\
                    ( HT086Measurable M G )
                  )
                  ->
                  (
                    I `
                    ( x e. U. dom M |->
                      ( ( F ` x ) +e ( G ` x ) ) )
                  )
                  =
                  ( ( I ` F ) +e ( I ` G ) )
                )
              /\
              (
                A. F A. G
                  (
                    (
                      F e. ( ( 0 [,] +oo ) ^m U. dom M )
                      /\
                      (
                        G e. ( ( 0 [,] +oo ) ^m U. dom M )
                        /\
                        ( HT086AE M F G )
                      )
                    )
                    ->
                    ( I ` F ) = ( I ` G )
                  )
                /\
                (
                  A. H A. G
                    (
                      (
                        (
                          A. n e. NN0
                            ( HT086Measurable M ( H ` n ) )
                          /\
                          A. n e. NN0 A. x e. U. dom M
                            ( ( H ` n ) ` x )
                            <_
                            ( ( H ` ( n + 1 ) ) ` x )
                        )
                        /\
                        ( HT086PointwiseSup M H G )
                      )
                      ->
                      ( I ` G )
                      =
                      sup
                      (
                        { y e. ( 0 [,] +oo ) |
                          E. n e. NN0 y = ( I ` ( H ` n ) )
                        } ,
                        RR* ,
                        <
                      )
                    )
                  /\
                  (
                    A. F
                      (
                        ( HT086Measurable M F )
                        ->
                        (
                          ( I ` F ) = 0
                          <->
                          (
                            HT086AE M F
                            ( x e. U. dom M |-> 0 )
                          )
                        )
                      )
                    /\
                    A. F
                      (
                        ( HT086Measurable M F )
                        ->
                        (
                          ( I ` F ) =/= 0
                          <->
                          (
                            M `
                            { x e. U. dom M |
                              ( F ` x ) =/= 0
                            }
                          )
                          =/= 0
                        )
                      )
                  )
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
  $d F I J M $.
  $d I J M $.

  hundred-theorems-086-lebesgue-measure-and-integration $a |- (
    A. M e. U. ran measures
      E. I
        (
          ( HT086Laws M I )
          /\
          A. J
            (
              ( HT086Laws M J )
              ->
              A. F
                (
                  ( HT086Measurable M F )
                  ->
                  ( J ` F ) = ( I ` F )
                )
            )
        )
  ) $.
$}
