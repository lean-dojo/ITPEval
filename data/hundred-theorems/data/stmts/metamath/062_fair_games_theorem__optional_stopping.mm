$(
  Statement-only formalization of "Fair Games Theorem (Optional Stopping)" from Hundred Theorems
  item 062. It includes the bounded-stopping-time characterization of submartingales and the
  martingale, submartingale, and supermartingale optional-stopping conclusions under each of
  the three standard sufficient conditions. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The definitions below are conservative abbreviations over set.mm objects.
  A probability space is P e. Prob, with event sigma-algebra dom P and sample
  space U. dom P. Real random variables use the set.mm construction rRndVar.

  HT062SimpleIntegral integrates a nonnegative finite-range measurable real
  function by summing its values times the P-measures of their fibers.
  HT062NnIntegral is the supremum, in the extended reals, of those simple
  integrals over all nonnegative simple functions bounded by its argument.
  HT062L1 P is exactly the real random variables whose absolute-value
  nonnegative integral is finite. HT062Integral P is the genuine signed real
  integral on that L1 domain, defined as the difference of the integrals of
  the positive and negative parts. Thus all expectations below are taken with
  respect to the arbitrary probability measure P; set.mm's itgm is not used.

  HT062Filtration says that F is an increasing sequence of sub-sigma-algebras
  of dom P, all on the same sample space. HT062Integrable says that every X_n
  belongs to HT062L1 P, and HT062Adapted says that X_n is measurable with
  respect to F_n.

  HT062Martingale expresses the usual conditional-expectation martingale law
  without taking conditional expectation as a primitive: for n <= m, X_n and
  X_m have equal integrals on every event of F_n. For integrable adapted real
  processes this is equivalent to E[X_m | F_n] = X_n almost surely.

  A stopping time T maps the sample space to NN0* = NN0 u. { +oo }, and
  { w | T(w) <= n } belongs to F_n for every n. HT062EverywhereBounded is the
  pointwise boundedness used by the Lean characterization. HT062Bounded allows
  a measurable null exceptional set and is the almost-sure boundedness used by
  condition (a) of the Rocq theorem. HT062Stopped evaluates X_(T(w))(w) at
  finite stopping values and uses zero at +oo, as in the Rocq source.

  The final $a assertions are the translated statements. There are no $p
  proof statements in this file.
$)

$c HT062Simple HT062SimpleIntegral HT062NnIntegral $.
$c HT062L1 HT062Integral $.
$c HT062Filtration HT062SigmaFinite HT062Integrable HT062Adapted $.
$c HT062Stopping HT062TimeLe HT062EverywhereBounded HT062Bounded HT062Finite $.
$c HT062UniformlyBounded HT062StoppingIntegrable $.
$c HT062BoundedIncrements HT062Conditions $.
$c HT062Martingale HT062Submartingale HT062Supermartingale HT062Stopped $.

ht062-simple-syntax $a wff ( HT062Simple P G ) $.
ht062-simple-integral-syntax $a class ( HT062SimpleIntegral P G ) $.
ht062-nn-integral-syntax $a class ( HT062NnIntegral P H ) $.
ht062-l1-syntax $a class ( HT062L1 P ) $.
ht062-integral-syntax $a class ( HT062Integral P ) $.
ht062-filtration-syntax $a wff ( HT062Filtration P F ) $.
ht062-sigma-finite-syntax $a wff ( HT062SigmaFinite P F ) $.
ht062-integrable-syntax $a wff ( HT062Integrable P X ) $.
ht062-adapted-syntax $a wff ( HT062Adapted F X ) $.
ht062-stopping-syntax $a wff ( HT062Stopping P F T ) $.
ht062-time-le-syntax $a wff ( HT062TimeLe P T U ) $.
ht062-everywhere-bounded-syntax $a wff ( HT062EverywhereBounded P T ) $.
ht062-bounded-syntax $a wff ( HT062Bounded P T ) $.
ht062-finite-syntax $a wff ( HT062Finite P T ) $.
ht062-uniformly-bounded-syntax $a wff ( HT062UniformlyBounded P X ) $.
ht062-stopping-integrable-syntax $a wff ( HT062StoppingIntegrable P T ) $.
ht062-bounded-increments-syntax $a wff ( HT062BoundedIncrements P X ) $.
ht062-conditions-syntax $a wff ( HT062Conditions P X T ) $.
ht062-martingale-syntax $a wff ( HT062Martingale P F X ) $.
ht062-submartingale-syntax $a wff ( HT062Submartingale P F X ) $.
ht062-supermartingale-syntax $a wff ( HT062Supermartingale P F X ) $.
ht062-stopped-syntax $a class ( HT062Stopped P X T ) $.

${
  $d G P x $.

  ht062-simple-definition $a |- (
    ( HT062Simple P G )
    <->
    (
      G e. ( dom P MblFnM BrSiga )
      /\
      (
        G : U. dom P --> RR
        /\
        (
          ran G e. Fin
          /\
          A. x e. U. dom P 0 <_ ( G ` x )
        )
      )
    )
  ) $.
$}

${
  $d G P y $.

  ht062-simple-integral-definition $a |- (
    HT062SimpleIntegral P G
    =
    sum_ y e. ( ran G \ { 0 } )
      ( y x. ( P ` ( `' G " { y } ) ) )
  ) $.
$}

${
  $d H P g r x $.

  ht062-nn-integral-definition $a |- (
    HT062NnIntegral P H
    =
    sup
    (
      { r e. RR |
        E. g
          (
            ( HT062Simple P g )
            /\
            (
              A. x e. U. dom P ( g ` x ) <_ ( H ` x )
              /\
              r = ( HT062SimpleIntegral P g )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d P h x $.

  ht062-l1-definition $a |- (
    HT062L1 P
    =
    { h e. ( rRndVar ` P ) |
      ( HT062NnIntegral P
        ( x e. U. dom P |-> ( abs ` ( h ` x ) ) )
      ) e. RR
    }
  ) $.
$}

${
  $d H P x $.

  ht062-integral-definition $a |- (
    HT062Integral P
    =
    ( H e. ( HT062L1 P ) |->
      (
        ( HT062NnIntegral P
          ( x e. U. dom P |->
            if ( 0 <_ ( H ` x ) , ( H ` x ) , 0 ) )
        )
        -
        ( HT062NnIntegral P
          ( x e. U. dom P |->
            if ( ( H ` x ) < 0 , -u ( H ` x ) , 0 ) )
        )
      )
    )
  ) $.
$}

${
  $d F P m n $.

  ht062-filtration-definition $a |- (
    ( HT062Filtration P F )
    <->
    (
      F : NN0 --> ( sigAlgebra ` U. dom P )
      /\
      (
        A. n e. NN0 ( F ` n ) C_ dom P
        /\
        A. n e. NN0 A. m e. NN0
          ( n <_ m -> ( F ` n ) C_ ( F ` m ) )
      )
    )
  ) $.
$}

${
  $d F P f k n $.

  ht062-sigma-finite-definition $a |- (
    ( HT062SigmaFinite P F )
    <->
    A. n e. NN0 E. f
      (
        f : NN0 --> ( F ` n )
        /\
        (
          U. ran f = U. dom P
          /\
          A. k e. NN0 ( P ` ( f ` k ) ) e. RR
        )
      )
  ) $.
$}

${
  $d P X n $.

  ht062-integrable-definition $a |- (
    ( HT062Integrable P X )
    <->
    (
      X : NN0 --> ( rRndVar ` P )
      /\
      A. n e. NN0 ( X ` n ) e. ( HT062L1 P )
    )
  ) $.
$}

${
  $d F X n $.

  ht062-adapted-definition $a |- (
    ( HT062Adapted F X )
    <->
    A. n e. NN0
      ( X ` n ) e. ( ( F ` n ) MblFnM BrSiga )
  ) $.
$}

${
  $d F P T n x $.

  ht062-stopping-definition $a |- (
    ( HT062Stopping P F T )
    <->
    (
      T : U. dom P --> NN0*
      /\
      A. n e. NN0
        { x e. U. dom P | ( T ` x ) <_ n } e. ( F ` n )
    )
  ) $.
$}

${
  $d P T U x $.

  ht062-time-le-definition $a |- (
    ( HT062TimeLe P T U )
    <->
    A. x e. U. dom P ( T ` x ) <_ ( U ` x )
  ) $.
$}

${
  $d P T n x $.

  ht062-everywhere-bounded-definition $a |- (
    ( HT062EverywhereBounded P T )
    <->
    E. n e. NN0 A. x e. U. dom P ( T ` x ) <_ n
  ) $.
$}

${
  $d P T n x z $.

  ht062-bounded-definition $a |- (
    ( HT062Bounded P T )
    <->
    E. n e. NN0 E. z e. dom P
      (
        ( P ` z ) = 0
        /\
        A. x e. ( U. dom P \ z ) ( T ` x ) <_ n
      )
  ) $.
$}

${
  $d P T x z $.

  ht062-finite-definition $a |- (
    ( HT062Finite P T )
    <->
    E. z e. dom P
      (
        ( P ` z ) = 0
        /\
        A. x e. ( U. dom P \ z ) ( T ` x ) e. NN0
      )
  ) $.
$}

${
  $d P X k n x z $.

  ht062-uniformly-bounded-definition $a |- (
    ( HT062UniformlyBounded P X )
    <->
    E. k e. RR A. n e. NN0 E. z e. dom P
      (
        ( P ` z ) = 0
        /\
        A. x e. ( U. dom P \ z )
          ( abs ` ( ( X ` n ) ` x ) ) < k
      )
  ) $.
$}

${
  $d P T x $.

  ht062-stopping-integrable-definition $a |- (
    ( HT062StoppingIntegrable P T )
    <->
    (
      ( HT062Finite P T )
      /\
      ( x e. U. dom P |->
          if ( ( T ` x ) e. NN0 , ( T ` x ) , 0 )
      ) e. ( HT062L1 P )
    )
  ) $.
$}

${
  $d P X k n x z $.

  ht062-bounded-increments-definition $a |- (
    ( HT062BoundedIncrements P X )
    <->
    E. k e. RR
      (
        0 <_ k
        /\
        A. n e. NN0 E. z e. dom P
          (
            ( P ` z ) = 0
            /\
            A. x e. ( U. dom P \ z )
              ( abs `
                (
                  ( ( X ` ( n + 1 ) ) ` x )
                  -
                  ( ( X ` n ) ` x )
                )
              ) <_ k
          )
      )
  ) $.
$}

${
  $d P T X $.

  ht062-conditions-definition $a |- (
    ( HT062Conditions P X T )
    <->
    (
      ( HT062Bounded P T )
      \/
      (
        (
          ( HT062Finite P T )
          /\
          ( HT062UniformlyBounded P X )
        )
        \/
        (
          ( HT062StoppingIntegrable P T )
          /\
          ( HT062BoundedIncrements P X )
        )
      )
    )
  ) $.
$}

${
  $d F P X a m n x $.

  ht062-martingale-definition $a |- (
    ( HT062Martingale P F X )
    <->
    A. n e. NN0 A. m e. NN0
      (
        n <_ m
        ->
        A. a e. ( F ` n )
          (
            ( HT062Integral P )
            `
            ( x e. U. dom P |->
              if ( x e. a , ( ( X ` m ) ` x ) , 0 ) )
          )
          =
          (
            ( HT062Integral P )
            `
            ( x e. U. dom P |->
              if ( x e. a , ( ( X ` n ) ` x ) , 0 ) )
          )
      )
  ) $.
$}

${
  $d F P X a m n x $.

  ht062-submartingale-definition $a |- (
    ( HT062Submartingale P F X )
    <->
    A. n e. NN0 A. m e. NN0
      (
        n <_ m
        ->
        A. a e. ( F ` n )
          (
            ( HT062Integral P )
            `
            ( x e. U. dom P |->
              if ( x e. a , ( ( X ` n ) ` x ) , 0 ) )
          )
          <_
          (
            ( HT062Integral P )
            `
            ( x e. U. dom P |->
              if ( x e. a , ( ( X ` m ) ` x ) , 0 ) )
          )
      )
  ) $.
$}

${
  $d F P X a m n x $.

  ht062-supermartingale-definition $a |- (
    ( HT062Supermartingale P F X )
    <->
    A. n e. NN0 A. m e. NN0
      (
        n <_ m
        ->
        A. a e. ( F ` n )
          (
            ( HT062Integral P )
            `
            ( x e. U. dom P |->
              if ( x e. a , ( ( X ` m ) ` x ) , 0 ) )
          )
          <_
          (
            ( HT062Integral P )
            `
            ( x e. U. dom P |->
              if ( x e. a , ( ( X ` n ) ` x ) , 0 ) )
          )
      )
  ) $.
$}

${
  $d P T X x $.

  ht062-stopped-definition $a |- (
    HT062Stopped P X T
    =
    ( x e. U. dom P |->
      if
      (
        ( T ` x ) e. NN0 ,
        ( ( X ` ( T ` x ) ) ` x ) ,
        0
      )
    )
  ) $.
$}

${
  $d F P X t u $.

  hundred-theorems-062-submartingale-characterization $a |- (
    (
      P e. Prob
      /\
      (
        ( HT062Filtration P F )
        /\
        (
          ( HT062SigmaFinite P F )
          /\
          (
            ( HT062Integrable P X )
            /\
            ( HT062Adapted F X )
          )
        )
      )
    )
    ->
    (
      ( HT062Submartingale P F X )
      <->
      A. t A. u
        (
          (
            ( HT062Stopping P F t )
            /\
            (
              ( HT062Stopping P F u )
              /\
              (
                ( HT062TimeLe P t u )
                /\
                ( HT062EverywhereBounded P u )
              )
            )
          )
          ->
          (
            ( ( HT062Integral P ) ` ( HT062Stopped P X t ) )
            <_
            ( ( HT062Integral P ) ` ( HT062Stopped P X u ) )
          )
        )
    )
  ) $.
$}

${
  $d F P T X $.

  hundred-theorems-062-stopped-integrable $a |- (
    (
      P e. Prob
      /\
      (
        ( HT062Filtration P F )
        /\
        (
          ( HT062Integrable P X )
          /\
          (
            ( HT062Adapted F X )
            /\
            (
              ( HT062Stopping P F T )
              /\
              ( HT062Conditions P X T )
            )
          )
        )
      )
    )
    ->
    ( HT062Stopped P X T ) e. ( HT062L1 P )
  ) $.

  hundred-theorems-062-optional-stopping $a |- (
    (
      P e. Prob
      /\
      (
        ( HT062Filtration P F )
        /\
        (
          ( HT062Integrable P X )
          /\
          (
            ( HT062Adapted F X )
            /\
            (
              ( HT062Martingale P F X )
              /\
              (
                ( HT062Stopping P F T )
                /\
                ( HT062Conditions P X T )
              )
            )
          )
        )
      )
    )
    ->
    (
      ( ( HT062Integral P ) ` ( HT062Stopped P X T ) )
      =
      ( ( HT062Integral P ) ` ( X ` 0 ) )
    )
  ) $.

  hundred-theorems-062-optional-stopping-sub $a |- (
    (
      P e. Prob
      /\
      (
        ( HT062Filtration P F )
        /\
        (
          ( HT062Integrable P X )
          /\
          (
            ( HT062Adapted F X )
            /\
            (
              ( HT062Submartingale P F X )
              /\
              (
                ( HT062Stopping P F T )
                /\
                ( HT062Conditions P X T )
              )
            )
          )
        )
      )
    )
    ->
    (
      ( ( HT062Integral P ) ` ( X ` 0 ) )
      <_
      ( ( HT062Integral P ) ` ( HT062Stopped P X T ) )
    )
  ) $.

  hundred-theorems-062-optional-stopping-super $a |- (
    (
      P e. Prob
      /\
      (
        ( HT062Filtration P F )
        /\
        (
          ( HT062Integrable P X )
          /\
          (
            ( HT062Adapted F X )
            /\
            (
              ( HT062Supermartingale P F X )
              /\
              (
                ( HT062Stopping P F T )
                /\
                ( HT062Conditions P X T )
              )
            )
          )
        )
      )
    )
    ->
    (
      ( ( HT062Integral P ) ` ( HT062Stopped P X T ) )
      <_
      ( ( HT062Integral P ) ` ( X ` 0 ) )
    )
  ) $.
$}
