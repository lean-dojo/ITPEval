$(
  Statement-only formalization of Thousand Theorems corpus artifact Q595466
  (thousand-theorems__metamath__Q595466), "Dini's theorem": a monotone family,
  indexed by an arbitrary preorder, of continuous functions from an arbitrary
  topological space to a normed lattice-ordered Abelian group with solid norm,
  converging pointwise along atTop to a continuous limit, converges locally
  uniformly. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q595466Preorder expands the arbitrary preorder on the index carrier.
  Q595466AtTop is the at-top filter itself: a set is eventual exactly when it
  contains a finite intersection of upper rays. This finite-intersection form
  is important for empty or nondirected preorders and agrees with Lean's
  infimum-of-principal-filters definition of atTop.

  The codomain is a SetMM normed Abelian group and lattice on one common
  structure. Q595466SolidNorm is precisely monotonicity of the norm under the
  lattice absolute value |a| = a join (-a), and Q595466OrderedAdd is
  monotonicity of left addition.

  Q595466PointwiseTendsto and Q595466LocallyUniform use the positive-radius
  metric criteria for convergence in the norm topology. The latter requires,
  at every domain point and radius, an open neighborhood on which the same
  atTop-event makes the convergence uniform.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q595466Preorder Q595466AtTop Q595466Sub Q595466LatticeAbs
   Q595466SolidNorm Q595466OrderedAdd Q595466Monotone
   Q595466PointwiseTendsto Q595466LocallyUniform $.

q595466-preorder-syntax
  $a wff ( Q595466Preorder I R ) $.
q595466-at-top-syntax
  $a class ( Q595466AtTop I R ) $.
q595466-sub-syntax
  $a class ( Q595466Sub G a b ) $.
q595466-lattice-abs-syntax
  $a class ( Q595466LatticeAbs G a ) $.
q595466-solid-norm-syntax
  $a wff ( Q595466SolidNorm G ) $.
q595466-ordered-add-syntax
  $a wff ( Q595466OrderedAdd G ) $.
q595466-monotone-syntax
  $a wff ( Q595466Monotone G I R X F ) $.
q595466-pointwise-tendsto-syntax
  $a wff ( Q595466PointwiseTendsto G I R F f x ) $.
q595466-locally-uniform-syntax
  $a wff ( Q595466LocallyUniform G I R X J F f ) $.

${
  $d I R i j k $.

  q595466-preorder-definition $a |- (
    ( Q595466Preorder I R )
    <->
    (
      R C_ ( I X. I )
      /\
      (
        A. i e. I <. i , i >. e. R
        /\
        A. i e. I A. j e. I A. k e. I
          (
            (
              <. i , j >. e. R
              /\
              <. j , k >. e. R
            )
            ->
            <. i , k >. e. R
          )
      )
    )
  ) $.
$}

${
  $d A I R S i k $.

  q595466-at-top-definition $a |- (
    ( Q595466AtTop I R )
    =
    { A e. ~P I |
      E. S e. ( ~P I i^i Fin )
        { k e. I |
          A. i e. S <. i , k >. e. R
        }
        C_ A
    }
  ) $.
$}

${
  $d G a b $.

  q595466-sub-definition $a |- (
    ( Q595466Sub G a b )
    =
    (
      a
      ( +g ` G )
      ( ( invg ` G ) ` b )
    )
  ) $.
$}

${
  $d G a $.

  q595466-lattice-abs-definition $a |- (
    ( Q595466LatticeAbs G a )
    =
    (
      a
      ( join ` G )
      ( ( invg ` G ) ` a )
    )
  ) $.
$}

${
  $d G a b $.

  q595466-solid-norm-definition $a |- (
    ( Q595466SolidNorm G )
    <->
    A. a e. ( Base ` G ) A. b e. ( Base ` G )
      (
        ( Q595466LatticeAbs G a )
        ( le ` G )
        ( Q595466LatticeAbs G b )
        ->
        ( ( norm ` G ) ` a )
        <_
        ( ( norm ` G ) ` b )
      )
  ) $.
$}

${
  $d G a b c $.

  q595466-ordered-add-definition $a |- (
    ( Q595466OrderedAdd G )
    <->
    A. a e. ( Base ` G ) A. b e. ( Base ` G )
      A. c e. ( Base ` G )
        (
          a ( le ` G ) b
          ->
          (
            c ( +g ` G ) a
          )
          ( le ` G )
          (
            c ( +g ` G ) b
          )
        )
  ) $.
$}

${
  $d F G I R X i j x $.

  q595466-monotone-definition $a |- (
    ( Q595466Monotone G I R X F )
    <->
    A. i e. I A. j e. I
      (
        <. i , j >. e. R
        ->
        A. x e. X
          (
            ( ( F ` i ) ` x )
            ( le ` G )
            ( ( F ` j ) ` x )
          )
      )
  ) $.
$}

${
  $d F G I R a f i x $.

  q595466-pointwise-tendsto-definition $a |- (
    ( Q595466PointwiseTendsto G I R F f x )
    <->
    A. a e. RR+
      { i e. I |
        (
          ( norm ` G )
          `
          (
            Q595466Sub
            G
            ( ( F ` i ) ` x )
            ( f ` x )
          )
        )
        <
        a
      }
      e. ( Q595466AtTop I R )
  ) $.
$}

${
  $d F G I J R U X a f i x y $.

  q595466-locally-uniform-definition $a |- (
    ( Q595466LocallyUniform G I R X J F f )
    <->
    A. a e. RR+ A. x e. X
      E. U e. J
        (
          x e. U
          /\
          { i e. I |
            A. y e. U
              (
                (
                  ( norm ` G )
                  `
                  (
                    Q595466Sub
                    G
                    ( ( F ` i ) ` y )
                    ( f ` y )
                  )
                )
                <
                a
              )
          }
          e. ( Q595466AtTop I R )
        )
  ) $.
$}

${
  $d F G I J R U X a b c f i j k x y $.

  thousand-theorems-q595466-dini $a |-
    A. I A. R A. X A. J A. G A. F A. f
      (
        (
          (
            ( Q595466Preorder I R )
            /\
            (
              J e. ( TopOn ` X )
              /\
              (
                G e. ( NrmGrp i^i Abel )
                /\
                (
                  G e. Lat
                  /\
                  (
                    ( Q595466SolidNorm G )
                    /\
                    ( Q595466OrderedAdd G )
                  )
                )
              )
            )
          )
          /\
          (
            F e. ( ( ( Base ` G ) ^m X ) ^m I )
            /\
            f e. ( ( Base ` G ) ^m X )
          )
        )
        ->
        (
          (
            (
              A. i e. I
                ( F ` i ) e. ( J Cn ( TopOpen ` G ) )
              /\
              ( Q595466Monotone G I R X F )
            )
            /\
            (
              f e. ( J Cn ( TopOpen ` G ) )
              /\
              A. x e. X
                ( Q595466PointwiseTendsto G I R F f x )
            )
          )
          ->
          ( Q595466LocallyUniform G I R X J F f )
        )
      )
  $.
$}
