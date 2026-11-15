$(
  Statement-only formalization of Thousand Theorems corpus artifact Q191693
  (thousand-theorems__metamath__Q191693), "Lebesgue's decomposition theorem":
  every s-finite measure has a decomposition, relative to any sigma-finite
  measure on the same measurable space, into a mutually singular measure and
  a measure with measurable extended-nonnegative density. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Q191693Simple and Q191693SimpleIntegral describe finite-range measurable
  extended-nonnegative simple functions and their integrals.
  Q191693LIntegral is the lower Lebesgue integral, defined as the supremum of
  the integrals of simple functions bounded by its argument.

  Q191693SFinite says that a measure is a countable pointwise sum of finite
  measures on the same sigma-algebra. Q191693SigmaFinite says that the carrier
  is covered by a countable family of measurable sets of finite measure.
  Q191693Measurable states measurability into the extended nonnegative reals,
  Q191693WithDensityValue is the value on a measurable set of the measure
  obtained by weighting N by F, and Q191693MutuallySingular expands the
  standard measure-theoretic predicate.

  Q191693HaveDecomposition keeps both source witnesses internal: a measure S
  on the same sigma-algebra and a measurable density F, with S mutually
  singular to N and M equal pointwise to S plus the density measure.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  root artifact contains no local $p declaration.
$)

$c Q191693Simple Q191693SimpleIntegral Q191693LIntegral
   Q191693Measurable Q191693WithDensityValue
   Q191693SFinite Q191693SigmaFinite Q191693MutuallySingular
   Q191693HaveDecomposition $.

q191693-simple-syntax $a wff ( Q191693Simple M G ) $.
q191693-simple-integral-syntax
  $a class ( Q191693SimpleIntegral M G ) $.
q191693-lintegral-syntax $a class ( Q191693LIntegral M H ) $.
q191693-measurable-syntax
  $a wff ( Q191693Measurable M F ) $.
q191693-with-density-value-syntax
  $a class ( Q191693WithDensityValue N F A ) $.
q191693-sfinite-syntax $a wff ( Q191693SFinite M ) $.
q191693-sigma-finite-syntax $a wff ( Q191693SigmaFinite N ) $.
q191693-mutually-singular-syntax
  $a wff ( Q191693MutuallySingular M N ) $.
q191693-have-decomposition-syntax
  $a wff ( Q191693HaveDecomposition M N ) $.

${
  $d G M $.

  q191693-simple-definition $a |- (
    ( Q191693Simple M G )
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

  q191693-simple-integral-definition $a |- (
    Q191693SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q191693-lintegral-definition $a |- (
    Q191693LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q191693Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q191693SimpleIntegral M G )
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

  q191693-measurable-definition $a |- (
    ( Q191693Measurable M F )
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

  q191693-with-density-value-definition $a |- (
    Q191693WithDensityValue N F A
  ) =
    (
      Q191693LIntegral
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
  $d A F M n $.

  q191693-sfinite-definition $a |- (
    ( Q191693SFinite M )
    <->
    E. F
      (
        F Fn NN0
        /\
        (
          A. n e. NN0
            (
              ( F ` n ) e. U. ran measures
              /\
              (
                dom ( F ` n ) = dom M
                /\
                ( ( F ` n ) ` U. dom M ) < +oo
              )
            )
          /\
          A. A e. dom M
            ( M ` A )
            =
            ( sum^ ` ( n e. NN0 |-> ( ( F ` n ) ` A ) ) )
        )
      )
  ) $.
$}

${
  $d F N n $.

  q191693-sigma-finite-definition $a |- (
    ( Q191693SigmaFinite N )
    <->
    E. F e. ( ( dom N ) ^m NN0 )
      (
        A. n e. NN0
          ( ( N ` ( F ` n ) ) < +oo )
        /\
        U. ran F = U. dom N
      )
  ) $.
$}

${
  $d A M N $.

  q191693-mutually-singular-definition $a |- (
    ( Q191693MutuallySingular M N )
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

  q191693-have-decomposition-definition $a |- (
    ( Q191693HaveDecomposition M N )
    <->
    (
      dom M = dom N
      /\
      E. S e. U. ran measures
        (
          dom S = dom M
          /\
          (
            ( Q191693MutuallySingular S N )
            /\
            E. F
              (
                ( Q191693Measurable N F )
                /\
                A. A e. dom M
                  ( M ` A )
                  =
                  (
                    ( S ` A )
                    +e
                    ( Q191693WithDensityValue N F A )
                  )
              )
          )
        )
    )
  ) $.
$}

${
  $d A F G H M N S n r x y $.

  thousand-theorems-q191693-lebesgue-decomposition $a |-
    A. M e. U. ran measures
      A. N e. U. ran measures
        (
          (
            dom M = dom N
            /\
            (
              ( Q191693SFinite M )
              /\
              ( Q191693SigmaFinite N )
            )
          )
          ->
          ( Q191693HaveDecomposition M N )
        )
  $.
$}
