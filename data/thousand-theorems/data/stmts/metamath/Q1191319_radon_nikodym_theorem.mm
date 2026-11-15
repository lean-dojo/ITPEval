$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1191319
  (thousand-theorems__metamath__Q1191319), "Radon-Nikodym theorem": for two
  arbitrary measures admitting a Lebesgue decomposition, absolute continuity
  is equivalent to equality with the measure having the chosen
  Radon-Nikodym density. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1191319Simple and Q1191319SimpleIntegral describe finite-range measurable
  extended-nonnegative simple functions and their integrals.
  Q1191319LIntegral is the lower Lebesgue integral, defined as the supremum of
  the integrals of simple functions bounded by its argument.

  Q1191319Measurable states measurability into the extended nonnegative reals,
  and Q1191319WithDensityValue is the value on a measurable set of the measure
  obtained by weighting N by F. Q1191319AbsolutelyContinuous and
  Q1191319MutuallySingular expand the standard measure-theoretic predicates.

  Q1191319RNDerivative M N F says that F is the density component of a
  Lebesgue decomposition of M relative to N. Q1191319HaveDecomposition is the
  existence of such a component. Lean's rnDeriv is a choice of exactly such a
  component. Any two components give the same density measure, so the
  internally existential Q1191319RNWithDensityEq is equivalent, under
  Q1191319HaveDecomposition, to
  N.withDensity (rnDeriv M N) = M.

  The final declaration is the single unproved corpus $a statement. In this
  root artifact, all preceding $a declarations are syntax or faithful
  definitions, and no $p proof statement is declared locally. The imported
  lib/set.mm database contains its standard verified proofs.
$)

$c Q1191319Simple Q1191319SimpleIntegral Q1191319LIntegral
   Q1191319Measurable Q1191319WithDensityValue
   Q1191319AbsolutelyContinuous Q1191319MutuallySingular
   Q1191319RNDerivative Q1191319HaveDecomposition
   Q1191319RNWithDensityEq $.

q1191319-simple-syntax $a wff ( Q1191319Simple M G ) $.
q1191319-simple-integral-syntax
  $a class ( Q1191319SimpleIntegral M G ) $.
q1191319-lintegral-syntax $a class ( Q1191319LIntegral M H ) $.
q1191319-measurable-syntax
  $a wff ( Q1191319Measurable M F ) $.
q1191319-with-density-value-syntax
  $a class ( Q1191319WithDensityValue N F A ) $.
q1191319-absolutely-continuous-syntax
  $a wff ( Q1191319AbsolutelyContinuous M N ) $.
q1191319-mutually-singular-syntax
  $a wff ( Q1191319MutuallySingular M N ) $.
q1191319-rn-derivative-syntax
  $a wff ( Q1191319RNDerivative M N F ) $.
q1191319-have-decomposition-syntax
  $a wff ( Q1191319HaveDecomposition M N ) $.
q1191319-rn-with-density-eq-syntax
  $a wff ( Q1191319RNWithDensityEq M N ) $.

${
  $d G M $.

  q1191319-simple-definition $a |- (
    ( Q1191319Simple M G )
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

  q1191319-simple-integral-definition $a |- (
    Q1191319SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q1191319-lintegral-definition $a |- (
    Q1191319LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1191319Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1191319SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d F M $.

  q1191319-measurable-definition $a |- (
    ( Q1191319Measurable M F )
    <->
    (
      F : U. dom M --> ( 0 [,] +oo )
      /\
      F e.
        (
          dom M
          MblFnM
          (
            sigaGen `
            ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
          )
        )
    )
  ) $.
$}

${
  $d A F N x $.

  q1191319-with-density-value-definition $a |- (
    Q1191319WithDensityValue N F A
  ) =
    (
      Q1191319LIntegral
      N
      ( x e. U. dom N |->
        if
        (
          x e. A ,
          ( F ` x ) ,
          0
        )
      )
    )
  $.
$}

${
  $d A M N $.

  q1191319-absolutely-continuous-definition $a |- (
    ( Q1191319AbsolutelyContinuous M N )
    <->
    (
      dom M = dom N
      /\
      A. A e. dom N
        (
          ( N ` A ) = 0
          ->
          ( M ` A ) = 0
        )
    )
  ) $.
$}

${
  $d A M N $.

  q1191319-mutually-singular-definition $a |- (
    ( Q1191319MutuallySingular M N )
    <->
    (
      dom M = dom N
      /\
      E. A e. dom N
        (
          ( M ` ( U. dom N \ A ) ) = 0
          /\
          ( N ` A ) = 0
        )
    )
  ) $.
$}

${
  $d A F M N S $.

  q1191319-rn-derivative-definition $a |- (
    ( Q1191319RNDerivative M N F )
    <->
    (
      dom M = dom N
      /\
      (
        ( Q1191319Measurable N F )
        /\
        E. S e. U. ran measures
          (
            dom S = dom M
            /\
            (
              ( Q1191319MutuallySingular S N )
              /\
              A. A e. dom M
                ( M ` A )
                =
                (
                  ( S ` A )
                  +e
                  ( Q1191319WithDensityValue N F A )
                )
            )
          )
      )
    )
  ) $.
$}

${
  $d F M N $.

  q1191319-have-decomposition-definition $a |- (
    ( Q1191319HaveDecomposition M N )
    <->
    E. F ( Q1191319RNDerivative M N F )
  ) $.
$}

${
  $d A F M N $.

  q1191319-rn-with-density-eq-definition $a |- (
    ( Q1191319RNWithDensityEq M N )
    <->
    E. F
      (
        ( Q1191319RNDerivative M N F )
        /\
        A. A e. dom M
          ( Q1191319WithDensityValue N F A )
          =
          ( M ` A )
      )
  ) $.
$}

${
  $d A F G H M N S r x y $.

  thousand-theorems-q1191319-radon-nikodym $a |-
    A. M e. U. ran measures
      A. N e. U. ran measures
        (
          ( Q1191319HaveDecomposition M N )
          ->
          (
            ( Q1191319AbsolutelyContinuous M N )
            <->
            ( Q1191319RNWithDensityEq M N )
          )
        )
  $.
$}
