$(
  Statement-only formalization of Thousand Theorems corpus artifact Q6813106
  (thousand-theorems__metamath__Q6813106), "Mellin inversion theorem": for a
  function from the reals to an arbitrary complex Banach space, the inverse
  Mellin transform recovers its value at a positive continuity point under
  Mellin convergence and vertical integrability assumptions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q6813106Restrict is zero extension from a subset of the real line, and
  Q6813106FunctionIntegrable encodes almost-everywhere strong measurability
  and finite L1 norm. Q6813106HasIntegral defines the Banach-valued Bochner
  integral by L1-approximation with measurable finite-range functions, and
  Q6813106TotalIntegral totalizes its unique value by zero.

  Q6813106MellinIntegrand W F S is t |-> t ^ (S - 1) . F(t), using SetMM's
  principal complex power and the scalar action of the complex normed space
  W. Mellin convergence is Bochner integrability of its restriction to the
  positive real axis. Q6813106Mellin is the corresponding totalized integral.

  Q6813106VerticalIntegrable W G R is integrability of
  y |-> G(R + i y). Q6813106MellinInv is (2 pi)^-1 times the Bochner integral
  of y |-> x ^ (-(R + i y)) . G(R + i y).

  Every declaration before the final one is syntax or an explicit faithful
  definition. The final $a declaration is the single unproved corpus
  statement, and this database contains no $p proof statement.
$)

$c Q6813106Restrict Q6813106Tendsto Q6813106AEStrong
   Q6813106Simple Q6813106SimpleIntegral Q6813106LIntegral
   Q6813106Diff Q6813106L1Distance Q6813106FunctionIntegrable
   Q6813106HasIntegral Q6813106TotalIntegral Q6813106ContinuousAt
   Q6813106MellinIntegrand Q6813106MellinConvergent Q6813106Mellin
   Q6813106VerticalIntegrable Q6813106MellinInv $.

q6813106-restrict-syntax
  $a class ( Q6813106Restrict W H A ) $.
q6813106-tendsto-syntax
  $a wff ( Q6813106Tendsto W S C ) $.
q6813106-aestrong-syntax
  $a wff ( Q6813106AEStrong M W H ) $.
q6813106-simple-syntax
  $a wff ( Q6813106Simple M G ) $.
q6813106-simple-integral-syntax
  $a class ( Q6813106SimpleIntegral M G ) $.
q6813106-lintegral-syntax
  $a class ( Q6813106LIntegral M H ) $.
q6813106-diff-syntax
  $a class ( Q6813106Diff M W H K ) $.
q6813106-l1-distance-syntax
  $a class ( Q6813106L1Distance M W H K ) $.
q6813106-function-integrable-syntax
  $a wff ( Q6813106FunctionIntegrable M W H ) $.
q6813106-has-integral-syntax
  $a wff ( Q6813106HasIntegral M W H y ) $.
q6813106-total-integral-syntax
  $a class ( Q6813106TotalIntegral W H ) $.
q6813106-continuous-at-syntax
  $a wff ( Q6813106ContinuousAt W F X ) $.
q6813106-mellin-integrand-syntax
  $a class ( Q6813106MellinIntegrand W F S ) $.
q6813106-mellin-convergent-syntax
  $a wff ( Q6813106MellinConvergent W F S ) $.
q6813106-mellin-syntax
  $a class ( Q6813106Mellin W F ) $.
q6813106-vertical-integrable-syntax
  $a wff ( Q6813106VerticalIntegrable W G R ) $.
q6813106-mellin-inv-syntax
  $a class ( Q6813106MellinInv W R G X ) $.

${
  $d A H W t $.

  q6813106-restrict-definition $a |- (
    Q6813106Restrict W H A
  ) =
    ( t e. RR |->
      if
      (
        t e. A ,
        ( H ` t ) ,
        ( 0g ` W )
      )
    )
  $.
$}

${
  $d C S W $.

  q6813106-tendsto-definition $a |- (
    ( Q6813106Tendsto W S C )
    <->
    (
      S : NN0 --> ( Base ` W )
      /\
      S ( ~~>t ` ( TopOpen ` W ) ) C
    )
  ) $.
$}

${
  $d H M N S W n x $.

  q6813106-aestrong-definition $a |- (
    ( Q6813106AEStrong M W H )
    <->
    (
      H e. ( ( Base ` W ) ^m U. dom M )
      /\
      E. S e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            (
              ( S ` n )
                e. ( dom M MblFnM ( sigaGen ` ( TopOpen ` W ) ) )
              /\
              ran ( S ` n ) e. Fin
            )
          /\
          E. N e. dom M
            (
              ( M ` N ) = 0
              /\
              A. x e. ( U. dom M \ N )
                (
                  Q6813106Tendsto
                  W
                  ( n e. NN0 |-> ( ( S ` n ) ` x ) )
                  ( H ` x )
                )
            )
        )
    )
  ) $.
$}

${
  $d G M $.

  q6813106-simple-definition $a |- (
    ( Q6813106Simple M G )
    <->
    (
      G : U. dom M --> ( 0 [,] +oo )
      /\
      (
        G e.
          (
            dom M
            MblFnM
            (
              sigaGen `
              ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
            )
          )
        /\
        ran G e. Fin
      )
    )
  ) $.
$}

${
  $d G M r $.

  q6813106-simple-integral-definition $a |- (
    Q6813106SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q6813106-lintegral-definition $a |- (
    Q6813106LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q6813106Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q6813106SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  $.
$}

${
  $d H K M W x $.

  q6813106-diff-definition $a |- (
    Q6813106Diff M W H K
  ) =
    ( x e. U. dom M |->
      (
        ( H ` x )
        ( +g ` W )
        ( ( -g ` W ) ` ( K ` x ) )
      )
    )
  $.
$}

${
  $d H K M W x $.

  q6813106-l1-distance-definition $a |- (
    Q6813106L1Distance M W H K
  ) =
    (
      Q6813106LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q6813106Diff M W H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M W x $.

  q6813106-function-integrable-definition $a |- (
    ( Q6813106FunctionIntegrable M W H )
    <->
    (
      ( Q6813106AEStrong M W H )
      /\
      (
        Q6813106LIntegral
        M
        ( x e. U. dom M |->
          ( ( norm ` W ) ` ( H ` x ) )
        )
      )
      < +oo
    )
  ) $.
$}

${
  $d H M S W n y $.

  q6813106-has-integral-definition $a |- (
    ( Q6813106HasIntegral M W H y )
    <->
    (
      y e. ( Base ` W )
      /\
      E. S e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            ( ( S ` n ) e. dom ( W sitg M ) )
          /\
          (
            Q6813106Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q6813106L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q6813106Tendsto
            W
            ( n e. NN0 |-> ( ( W sitg M ) ` ( S ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d H W y $.

  q6813106-total-integral-definition $a |- (
    Q6813106TotalIntegral W H
  ) =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q6813106FunctionIntegrable vol W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q6813106HasIntegral vol W H y )
      ) ,
      ( 0g ` W )
    )
  $.
$}

${
  $d F O U W X t $.

  q6813106-continuous-at-definition $a |- (
    ( Q6813106ContinuousAt W F X )
    <->
    A. O e. ( TopOpen ` W )
      (
        ( F ` X ) e. O
        ->
        E. U e. ( TopOpen ` RRfld )
          (
            X e. U
            /\
            A. t e. U ( F ` t ) e. O
          )
      )
  ) $.
$}

${
  $d F S W t $.

  q6813106-mellin-integrand-definition $a |- (
    Q6813106MellinIntegrand W F S
  ) =
    ( t e. RR |->
      (
        ( t ^c ( S - 1 ) )
        ( .s ` W )
        ( F ` t )
      )
    )
  $.
$}

${
  $d F S W $.

  q6813106-mellin-convergent-definition $a |- (
    ( Q6813106MellinConvergent W F S )
    <->
    (
      Q6813106FunctionIntegrable
      vol
      W
      (
        Q6813106Restrict
        W
        ( Q6813106MellinIntegrand W F S )
        RR+
      )
    )
  ) $.
$}

${
  $d F S W $.

  q6813106-mellin-definition $a |- (
    Q6813106Mellin W F
  ) =
    ( S e. CC |->
      (
        Q6813106TotalIntegral
        W
        (
          Q6813106Restrict
          W
          ( Q6813106MellinIntegrand W F S )
          RR+
        )
      )
    )
  $.
$}

${
  $d G R W y $.

  q6813106-vertical-integrable-definition $a |- (
    ( Q6813106VerticalIntegrable W G R )
    <->
    (
      Q6813106FunctionIntegrable
      vol
      W
      ( y e. RR |->
        ( G ` ( R + ( y x. _i ) ) )
      )
    )
  ) $.
$}

${
  $d G R W X y $.

  q6813106-mellin-inv-definition $a |- (
    Q6813106MellinInv W R G X
  ) =
    (
      ( 1 / ( 2 x. _pi ) )
      ( .s ` W )
      (
        Q6813106TotalIntegral
        W
        ( y e. RR |->
          (
            (
              X
              ^c
              ( -u ( R + ( y x. _i ) ) )
            )
            ( .s ` W )
            ( G ` ( R + ( y x. _i ) ) )
          )
        )
      )
    )
  $.
$}

${
  $d F R W X w $.

  thousand-theorems-q6813106-mellin-inversion $a |-
    A. W e.
      {
        w e. Ban |
        ( Scalar ` w ) = CCfld
      }
      A. R e. RR
        A. F e. ( ( Base ` W ) ^m RR )
          A. X e. RR
            (
              (
                (
                  0 < X
                  /\
                  ( Q6813106MellinConvergent W F R )
                )
                /\
                (
                  Q6813106VerticalIntegrable
                  W
                  ( Q6813106Mellin W F )
                  R
                )
                /\
                ( Q6813106ContinuousAt W F X )
              )
              ->
              (
                Q6813106MellinInv
                W
                R
                ( Q6813106Mellin W F )
                X
              )
              =
              ( F ` X )
            )
  $.
$}
