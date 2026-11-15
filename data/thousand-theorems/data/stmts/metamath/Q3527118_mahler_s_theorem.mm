$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527118
  (thousand-theorems__metamath__Q3527118), "Mahler's theorem": for every
  prime p, every complete ultrametric normed additive commutative group that
  is a bounded module over the p-adic integers, and every continuous
  p-adic-integer-valued-domain function f, the Mahler series whose nth
  coefficient is the nth forward difference of f at zero converges uniformly
  to f. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q3527118PadicInt p P characterizes the p-adic integer ring as a complete
  ultrametric commutative normed ring with dense integer image and with the
  p-adic norm on that image. This is the completion characterization of
  Lean's bundled ring Z_[p].

  Q3527118Module P E states the source hypotheses that E is a complete
  ultrametric normed additive commutative group, a P-module, and has bounded
  scalar multiplication. Q3527118Continuous is metric continuity.

  Q3527118Mahler P n is the unique continuous P-valued function on P whose
  value at each natural k is the cast of k choose n. Q3527118FwdDiff expands
  the nth forward difference at zero as the standard finite alternating
  binomial sum. Q3527118HasSum is convergence of the finite-subset net in the
  uniform norm, exactly the HasSum topology on continuous maps.

  Every declaration below is an unproved $a statement encoding syntax, a
  faithful definition, or the final corpus statement. There is no $p proof.
$)

$c Q3527118Sub Q3527118Complete Q3527118Ultrametric
   Q3527118PadicInt Q3527118Module Q3527118Continuous
   Q3527118Mahler Q3527118FwdDiff Q3527118Term Q3527118HasSum $.

q3527118-sub-syntax
  $a class ( Q3527118Sub E x y ) $.
q3527118-complete-syntax
  $a wff ( Q3527118Complete E ) $.
q3527118-ultrametric-syntax
  $a wff ( Q3527118Ultrametric E ) $.
q3527118-padic-int-syntax
  $a wff ( Q3527118PadicInt p P ) $.
q3527118-module-syntax
  $a wff ( Q3527118Module P E ) $.
q3527118-continuous-syntax
  $a wff ( Q3527118Continuous P E f ) $.
q3527118-mahler-syntax
  $a class ( Q3527118Mahler P n ) $.
q3527118-forward-difference-syntax
  $a class ( Q3527118FwdDiff P E f n ) $.
q3527118-term-syntax
  $a class ( Q3527118Term P E f n ) $.
q3527118-has-sum-syntax
  $a wff ( Q3527118HasSum P E f ) $.

${
  $d E x y $.

  q3527118-sub-definition $a |- (
    Q3527118Sub E x y
  ) = (
    x
    ( +g ` E )
    ( ( -g ` E ) ` y )
  ) $.
$}

${
  $d E e h m n q x $.

  q3527118-complete-definition $a |- (
    ( Q3527118Complete E )
    <->
    A. h e. ( ( Base ` E ) ^m NN0 )
      (
        (
          A. e e. RR+
            E. q e. NN0
              A. m e. ( ZZ>= ` q )
                A. n e. ( ZZ>= ` q )
                  (
                    ( norm ` E )
                    `
                    (
                      Q3527118Sub E
                        ( h ` m )
                        ( h ` n )
                    )
                  )
                  <
                  e
        )
        ->
        E. x e. ( Base ` E )
          A. e e. RR+
            E. q e. NN0
              A. m e. ( ZZ>= ` q )
                (
                  ( norm ` E )
                  `
                  (
                    Q3527118Sub E
                      ( h ` m )
                      x
                  )
                )
                <
                e
      )
  ) $.
$}

${
  $d E x y $.

  q3527118-ultrametric-definition $a |- (
    ( Q3527118Ultrametric E )
    <->
    A. x e. ( Base ` E )
      A. y e. ( Base ` E )
        (
          ( norm ` E )
          `
          ( x ( +g ` E ) y )
        )
        <_
        if (
          (
            ( ( norm ` E ) ` x )
            <_
            ( ( norm ` E ) ` y )
          )
          ,
          ( ( norm ` E ) ` y )
          ,
          ( ( norm ` E ) ` x )
        )
  ) $.
$}

${
  $d P e p x z $.

  q3527118-padic-int-definition $a |- (
    ( Q3527118PadicInt p P )
    <->
    (
      P e. ( NrmRing i^i CRing )
      /\
      ( Q3527118Complete P )
      /\
      ( Q3527118Ultrametric P )
      /\
      A. z e. ZZ
        (
          ( norm ` P )
          `
          ( ( ZRHom ` P ) ` z )
        )
        =
        if (
          z = 0
          ,
          0
          ,
          ( p ^ -u ( p pCnt z ) )
        )
      /\
      A. x e. ( Base ` P )
        A. e e. RR+
          E. z e. ZZ
            (
              ( norm ` P )
              `
              (
                Q3527118Sub P
                  x
                  ( ( ZRHom ` P ) ` z )
              )
            )
            <
            e
    )
  ) $.
$}

${
  $d E P a x $.

  q3527118-module-definition $a |- (
    ( Q3527118Module P E )
    <->
    (
      E e. ( NrmGrp i^i LMod )
      /\
      ( Scalar ` E ) = P
      /\
      ( Q3527118Complete E )
      /\
      ( Q3527118Ultrametric E )
      /\
      A. a e. ( Base ` P )
        A. x e. ( Base ` E )
          (
            ( norm ` E )
            `
            ( a ( .s ` E ) x )
          )
          <_
          (
            ( ( norm ` P ) ` a )
            x.
            ( ( norm ` E ) ` x )
          )
    )
  ) $.
$}

${
  $d E P d e f x y $.

  q3527118-continuous-definition $a |- (
    ( Q3527118Continuous P E f )
    <->
    (
      f : ( Base ` P ) --> ( Base ` E )
      /\
      A. x e. ( Base ` P )
        A. e e. RR+
          E. d e. RR+
            A. y e. ( Base ` P )
              (
                (
                  ( norm ` P )
                  `
                  ( Q3527118Sub P y x )
                )
                <
                d
                ->
                (
                  ( norm ` E )
                  `
                  (
                    Q3527118Sub E
                      ( f ` y )
                      ( f ` x )
                  )
                )
                <
                e
              )
    )
  ) $.
$}

${
  $d P k m n $.

  q3527118-mahler-definition $a |- (
    Q3527118Mahler P n
  ) = (
    iota_ m e. ( ( Base ` P ) ^m ( Base ` P ) )
      (
        ( Q3527118Continuous P P m )
        /\
        A. k e. NN0
          (
            m
            `
            ( ( ZRHom ` P ) ` k )
          )
          =
          (
            ( ZRHom ` P )
            `
            ( k _C n )
          )
      )
  ) $.
$}

${
  $d E P f k n $.

  q3527118-forward-difference-definition $a |- (
    Q3527118FwdDiff P E f n
  ) = (
    E gsum
      (
        k e. ( 0 ... n ) |->
          (
            (
              ( ZRHom ` P )
              `
              (
                (
                  ( -u 1 )
                  ^
                  ( n - k )
                )
                x.
                ( n _C k )
              )
            )
            ( .s ` E )
            (
              f
              `
              ( ( ZRHom ` P ) ` k )
            )
          )
      )
  ) $.
$}

${
  $d E P f n x $.

  q3527118-term-definition $a |- (
    Q3527118Term P E f n
  ) = (
    x e. ( Base ` P ) |->
      (
        (
          ( Q3527118Mahler P n )
          `
          x
        )
        ( .s ` E )
        ( Q3527118FwdDiff P E f n )
      )
  ) $.
$}

${
  $d E P e f n s t x $.

  q3527118-has-sum-definition $a |- (
    ( Q3527118HasSum P E f )
    <->
    A. e e. RR+
      E. s e. ( ~P NN0 i^i Fin )
        A. t e. ( ~P NN0 i^i Fin )
          (
            s C_ t
            ->
            A. x e. ( Base ` P )
              (
                ( norm ` E )
                `
                (
                  Q3527118Sub E
                    (
                      E gsum
                        (
                          n e. t |->
                            (
                              ( Q3527118Term P E f n )
                              `
                              x
                            )
                        )
                    )
                    ( f ` x )
                )
              )
              <
              e
          )
  ) $.
$}

${
  $d f p q w $.

  thousand-theorems-q3527118-mahler-s-theorem $a |-
    A. p e. Prime
      A. q
        A. w
          A. f
            (
              (
                ( Q3527118PadicInt p q )
                /\
                ( Q3527118Module q w )
                /\
                ( Q3527118Continuous q w f )
              )
              ->
              ( Q3527118HasSum q w f )
            )
  $.
$}
