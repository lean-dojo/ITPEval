$(
  Statement-only formalization of Thousand Theorems corpus artifact Q9993851
  (thousand-theorems__metamath__Q9993851), "Lax-Milgram theorem": every
  coercive bounded bilinear form on an arbitrary real Hilbert space induces a
  continuous linear equivalence characterized by the corresponding
  inner-product identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q9993851BoundedBilinear W B is the uncurried form of a bounded real
  bilinear map on W. The two additive and homogeneous laws give linearity in
  each argument, and the global product-of-norms bound is equivalent to
  continuity of the corresponding curried bilinear map.

  Q9993851Coercive W B is exactly the source IsCoercive predicate: a strictly
  positive real constant bounds B(x,x) below by that constant times the
  square of the norm.

  SetMM's inner product is linear in its first slot, opposite to mathlib's
  convention, so y ( .i ` W ) ( T ` x ) renders mathlib's inner product of
  T x with y. Q9993851Associated W B T therefore states that T is precisely
  InnerProductSpace.continuousLinearMapOfBilin B.

  Q9993851ContinuousLinearEquiv W T requires T and its inverse to be bounded
  linear maps and T to be a bijection of the full carrier. This is exactly a
  continuous linear equivalence from W to W. The final declaration is the
  single unproved corpus statement. All preceding $a declarations are syntax
  or faithful bidirectional definitions. This root artifact has no $p
  declaration; the included lib/set.mm supplies proved statements.
$)

$c Q9993851BoundedBilinear Q9993851Coercive Q9993851Associated
   Q9993851ContinuousLinearEquiv $.

q9993851-bounded-bilinear-syntax
  $a wff ( Q9993851BoundedBilinear W B ) $.
q9993851-coercive-syntax
  $a wff ( Q9993851Coercive W B ) $.
q9993851-associated-syntax
  $a wff ( Q9993851Associated W B T ) $.
q9993851-continuous-linear-equiv-syntax
  $a wff ( Q9993851ContinuousLinearEquiv W T ) $.

${
  $d B C W a x y z $.

  q9993851-bounded-bilinear-definition $a |- (
    ( Q9993851BoundedBilinear W B )
    <->
    (
      B : ( ( Base ` W ) X. ( Base ` W ) ) --> RR
      /\
      (
        A. x e. ( Base ` W )
          A. y e. ( Base ` W )
            A. z e. ( Base ` W )
              (
                B ` <. ( x ( +g ` W ) y ) , z >.
              )
              =
              (
                ( B ` <. x , z >. )
                +
                ( B ` <. y , z >. )
              )
        /\
        (
          A. a e. RR
            A. x e. ( Base ` W )
              A. y e. ( Base ` W )
                (
                  B ` <. ( a ( .s ` W ) x ) , y >.
                )
                =
                (
                  a
                  x.
                  ( B ` <. x , y >. )
                )
          /\
          (
            A. x e. ( Base ` W )
              A. y e. ( Base ` W )
                A. z e. ( Base ` W )
                  (
                    B ` <. x , ( y ( +g ` W ) z ) >.
                  )
                  =
                  (
                    ( B ` <. x , y >. )
                    +
                    ( B ` <. x , z >. )
                  )
            /\
            (
              A. a e. RR
                A. x e. ( Base ` W )
                  A. y e. ( Base ` W )
                    (
                      B ` <. x , ( a ( .s ` W ) y ) >.
                    )
                    =
                    (
                      a
                      x.
                      ( B ` <. x , y >. )
                    )
              /\
              E. C e. RR
                (
                  0 <_ C
                  /\
                  A. x e. ( Base ` W )
                    A. y e. ( Base ` W )
                      (
                        abs
                        `
                        ( B ` <. x , y >. )
                      )
                      <_
                      (
                        (
                          C
                          x.
                          ( ( norm ` W ) ` x )
                        )
                        x.
                        ( ( norm ` W ) ` y )
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
  $d B C W x $.

  q9993851-coercive-definition $a |- (
    ( Q9993851Coercive W B )
    <->
    E. C e. RR
      (
        0 < C
        /\
        A. x e. ( Base ` W )
          (
            (
              C
              x.
              ( ( norm ` W ) ` x )
            )
            x.
            ( ( norm ` W ) ` x )
          )
          <_
          ( B ` <. x , x >. )
      )
  ) $.
$}

${
  $d B T W x y $.

  q9993851-associated-definition $a |- (
    ( Q9993851Associated W B T )
    <->
    A. x e. ( Base ` W )
      A. y e. ( Base ` W )
        (
          y
          ( .i ` W )
          ( T ` x )
        )
        =
        ( B ` <. x , y >. )
  ) $.
$}

q9993851-continuous-linear-equiv-definition $a |- (
  ( Q9993851ContinuousLinearEquiv W T )
  <->
  (
    T e. ( W NMHom W )
    /\
    (
      T : ( Base ` W ) -1-1-onto-> ( Base ` W )
      /\
      `' T e. ( W NMHom W )
    )
  )
) $.

${
  $d B T W $.

  thousand-theorems-q9993851-lax-milgram $a |-
    A. W e. CHil
      (
        ( Scalar ` W ) = RRfld
        ->
        A. B
          (
            (
              ( Q9993851BoundedBilinear W B )
              /\
              ( Q9993851Coercive W B )
            )
            ->
            E. T
              (
                ( Q9993851ContinuousLinearEquiv W T )
                /\
                ( Q9993851Associated W B T )
              )
          )
      )
  $.
$}
