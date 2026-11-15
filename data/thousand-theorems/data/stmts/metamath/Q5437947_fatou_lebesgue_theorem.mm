$(
  Statement-only formalization of Thousand Theorems corpus artifact Q5437947
  (thousand-theorems__metamath__Q5437947), "Fatou&ndash;Lebesgue theorem":
  for every sequence of measurable extended-nonnegative functions on an
  arbitrary measure space, the lower Lebesgue integral of the pointwise
  inferior limit is at most the inferior limit of the lower Lebesgue
  integrals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q5437947Simple and Q5437947SimpleIntegral describe finite-range measurable
  extended-nonnegative simple functions and their integrals.
  Q5437947LIntegral is the lower Lebesgue integral, defined as the supremum
  of the integrals of simple functions bounded pointwise by its argument.

  SetMM's native liminf applies to extended-real functions on unbounded
  subsets of the reals. Applied to an NN0-indexed function, its real tails
  select exactly the natural-number tails, so it is the source atTop liminf.
  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q5437947Simple Q5437947SimpleIntegral Q5437947LIntegral $.

q5437947-simple-syntax $a wff ( Q5437947Simple M G ) $.
q5437947-simple-integral-syntax
  $a class ( Q5437947SimpleIntegral M G ) $.
q5437947-lintegral-syntax $a class ( Q5437947LIntegral M H ) $.

${
  $d G M $.

  q5437947-simple-definition $a |- (
    ( Q5437947Simple M G )
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

  q5437947-simple-integral-definition $a |- (
    Q5437947SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d H M g x y $.

  q5437947-lintegral-definition $a |- (
    Q5437947LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. g
          (
            ( Q5437947Simple M g )
            /\
            (
              A. x e. U. dom M
                ( g ` x ) <_ ( H ` x )
              /\
              y = ( Q5437947SimpleIntegral M g )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d f m n x $.

  thousand-theorems-q5437947-fatou-lebesgue $a |-
    A. m e. U. ran measures
      A. f e.
        ( ( ( 0 [,] +oo ) ^m U. dom m ) ^m NN0 )
        (
          A. n e. NN0
            ( f ` n ) e.
              (
                dom m
                MblFnM
                (
                  sigaGen `
                  ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
                )
              )
          ->
          (
            Q5437947LIntegral
            m
            (
              x e. U. dom m |->
                (
                  liminf `
                  ( n e. NN0 |-> ( ( f ` n ) ` x ) )
                )
            )
          )
          <_
          (
            liminf `
            ( n e. NN0 |->
              ( Q5437947LIntegral m ( f ` n ) ) )
          )
        )
  $.
$}
