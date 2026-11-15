$(
  Statement-only formalization of Thousand Theorems corpus artifact Q576478
  (thousand-theorems__metamath__Q576478), "Liouville's theorem (complex
  analysis)": every globally complex-Frechet-differentiable function between
  arbitrary complex normed vector spaces whose range is bounded is constant,
  expressed by equality at every pair of domain points. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  V and W range over arbitrary SetMM normed vector spaces over CCfld.
  Q576478ContinuousLinear says that L is a complex-linear map with a finite
  global operator bound. Q576478HasFDerivAt is the epsilon-delta form of the
  Frechet remainder estimate, and Q576478Differentiable requires such a
  continuous complex-linear derivative at every point of V.

  Q576478BoundedRange is a uniform real norm bound on all values of F,
  equivalent to boundedness of the range in a normed space. The final
  unproved $a assertion universally quantifies the spaces, function, and two
  domain points. All preceding $a declarations are syntax or faithful
  bidirectional definitions; there is no $p proof statement.
$)

$c Q576478Sub Q576478ContinuousLinear Q576478HasFDerivAt
   Q576478Differentiable Q576478BoundedRange $.

q576478-sub-syntax $a class ( Q576478Sub V x y ) $.
q576478-continuous-linear-syntax
  $a wff ( Q576478ContinuousLinear V W L ) $.
q576478-has-fderiv-at-syntax
  $a wff ( Q576478HasFDerivAt V W F x L ) $.
q576478-differentiable-syntax
  $a wff ( Q576478Differentiable V W F ) $.
q576478-bounded-range-syntax
  $a wff ( Q576478BoundedRange W F ) $.

${
  $d V x y $.

  q576478-sub-definition $a |- (
    Q576478Sub V x y
  ) = (
    x
    ( +g ` V )
    ( ( invg ` V ) ` y )
  ) $.
$}

${
  $d C L V W u $.

  q576478-continuous-linear-definition $a |- (
    ( Q576478ContinuousLinear V W L )
    <->
    (
      L e. ( V LMHom W )
      /\
      E. C e. ( 0 [,) +oo )
        A. u e. ( Base ` V )
          (
            ( ( norm ` W ) ` ( L ` u ) )
            <_
            (
              C
              x.
              ( ( norm ` V ) ` u )
            )
          )
    )
  ) $.
$}

${
  $d F L V W d e x y $.

  q576478-has-fderiv-at-definition $a |- (
    ( Q576478HasFDerivAt V W F x L )
    <->
    A. e e. RR+
      E. d e. RR+
        A. y e. ( Base ` V )
          (
            (
              ( ( norm ` V ) ` ( Q576478Sub V y x ) )
              <
              d
            )
            ->
            (
              (
                ( norm ` W )
                `
                (
                  Q576478Sub
                  W
                  ( Q576478Sub W ( F ` y ) ( F ` x ) )
                  ( L ` ( Q576478Sub V y x ) )
                )
              )
              <_
              (
                e
                x.
                ( ( norm ` V ) ` ( Q576478Sub V y x ) )
              )
            )
          )
  ) $.
$}

${
  $d F L V W x $.

  q576478-differentiable-definition $a |- (
    ( Q576478Differentiable V W F )
    <->
    A. x e. ( Base ` V )
      E. L
        (
          ( Q576478ContinuousLinear V W L )
          /\
          ( Q576478HasFDerivAt V W F x L )
        )
  ) $.
$}

${
  $d C F W x $.

  q576478-bounded-range-definition $a |- (
    ( Q576478BoundedRange W F )
    <->
    E. C e. RR
      A. x e. dom F
        ( ( norm ` W ) ` ( F ` x ) ) <_ C
  ) $.
$}

${
  $d F V W w z $.

  thousand-theorems-q576478-liouville $a |-
    A. V e. { v e. NrmVec | ( Scalar ` v ) = CCfld }
      A. W e. { w e. NrmVec | ( Scalar ` w ) = CCfld }
        A. F e. ( ( Base ` W ) ^m ( Base ` V ) )
          A. z e. ( Base ` V )
            A. w e. ( Base ` V )
              (
                (
                  ( Q576478Differentiable V W F )
                  /\
                  ( Q576478BoundedRange W F )
                )
                ->
                ( F ` z ) = ( F ` w )
              )
  $.
$}
