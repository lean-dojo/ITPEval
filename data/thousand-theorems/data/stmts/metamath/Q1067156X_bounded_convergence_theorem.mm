$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1067156X
  (thousand-theorems__metamath__Q1067156X), "Bounded convergence theorem":
  uniformly bounded nonnegative bounded continuous functions converging along
  a countably generated filter have convergent lower Lebesgue integrals for a
  finite measure; the sequence specialization uses pointwise convergence at
  infinity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The nonnegative reals are ( 0 [,) +oo ), with their real subspace topology.
  The extended nonnegative reals are ( 0 [,] +oo ), with the topology inherited
  from the extended-real structure RR*s.

  Q1067156XCountablyGenerated gives a filter a countable refinement basis.
  Q1067156XBoundedContinuous is the actual class of continuous nonnegative
  functions with bounded range. Q1067156XAE M S says that S contains the
  complement of a measurable M-null set, allowing S itself to be arbitrary
  and matching Lean's completion-aware almost-everywhere filter.
  Q1067156XSimple and Q1067156XSimpleIntegral describe finite-range measurable
  extended-nonnegative simple functions and their extended-nonnegative
  integrals. Q1067156XLIntegral is the usual lower Lebesgue integral, defined
  as the supremum of simple integrals below a function; a nonnegative-real
  function is included canonically in the extended nonnegative reals.

  Q1067156XNatAtTop is the eventual-tail filter on NN0. The final two unproved
  $a declarations encode respectively the general countably generated filter
  theorem and its NN0-indexed pointwise specialization. All preceding $a
  declarations are syntax or faithful definitions.
$)

$c Q1067156XCountablyGenerated Q1067156XBoundedContinuous Q1067156XAE
   Q1067156XSimple Q1067156XSimpleIntegral Q1067156XLIntegral
   Q1067156XNatAtTop $.

q1067156x-countably-generated-syntax
  $a wff ( Q1067156XCountablyGenerated L Y ) $.
q1067156x-bounded-continuous-syntax
  $a wff ( Q1067156XBoundedContinuous J H ) $.
q1067156x-ae-syntax $a wff ( Q1067156XAE M S ) $.
q1067156x-simple-syntax $a wff ( Q1067156XSimple M G ) $.
q1067156x-simple-integral-syntax
  $a class ( Q1067156XSimpleIntegral M G ) $.
q1067156x-lintegral-syntax $a class ( Q1067156XLIntegral M H ) $.
q1067156x-nat-at-top-syntax $a class Q1067156XNatAtTop $.

${
  $d A B L Y n $.

  q1067156x-countably-generated-definition $a |- (
    ( Q1067156XCountablyGenerated L Y )
    <->
    E. B
      (
        B : NN0 --> L
        /\
        A. A e. L E. n e. NN0 ( B ` n ) C_ A
      )
  ) $.
$}

${
  $d M N S $.

  q1067156x-ae-definition $a |- (
    ( Q1067156XAE M S )
    <->
    E. N e. dom M
      (
        ( M ` N ) = 0
        /\
        ( U. dom M \ N ) C_ S
      )
  ) $.
$}

${
  $d H J d x $.

  q1067156x-bounded-continuous-definition $a |- (
    ( Q1067156XBoundedContinuous J H )
    <->
    (
      H e.
        (
          J
          Cn
          ( ( TopOpen ` RRfld ) |`t ( 0 [,) +oo ) )
        )
      /\
      E. d e. ( 0 [,) +oo )
        A. x e. U. J ( H ` x ) <_ d
    )
  ) $.
$}

${
  $d G M $.

  q1067156x-simple-definition $a |- (
    ( Q1067156XSimple M G )
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

  q1067156x-simple-integral-definition $a |- (
    Q1067156XSimpleIntegral M G
    =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  ) $.
$}

${
  $d G H M x y $.

  q1067156x-lintegral-definition $a |- (
    Q1067156XLIntegral M H
    =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1067156XSimple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1067156XSimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d A k n $.

  q1067156x-nat-at-top-definition $a |- Q1067156XNatAtTop =
    { A e. ~P NN0 |
      E. n e. NN0
        A. k e. NN0 ( n <_ k -> k e. A )
    } $.
$}

${
  $d A B F G H J L M Y c d f i k n r x y $.

  thousand-theorems-q1067156x-filter-bounded-convergence $a |-
    A. M e. U. ran measures
      A. J e. ( TopOn ` U. dom M )
        A. Y A. L A. F A. c A. f
          (
            (
              (
                ( M ` U. dom M ) e. ( 0 [,) +oo )
                /\
                J C_ dom M
              )
              /\
              (
                L e. ( Fil ` Y )
                /\
                ( Q1067156XCountablyGenerated L Y )
              )
            )
            ->
            (
              (
                (
                  c e. ( 0 [,) +oo )
                  /\
                  (
                    F : Y --> ( ( 0 [,) +oo ) ^m U. dom M )
                    /\
                    A. i e. Y
                      ( Q1067156XBoundedContinuous J ( F ` i ) )
                  )
                )
                /\
                f : U. dom M --> ( 0 [,) +oo )
              )
              ->
              (
                (
                  (
                    { i e. Y |
                      ( Q1067156XAE
                        M
                        { x e. U. dom M |
                          ( ( F ` i ) ` x ) <_ c
                        }
                      )
                    } e. L
                    /\
                    ( Q1067156XAE
                      M
                      { x e. U. dom M |
                        ( f ` x ) e.
                          (
                            (
                              (
                                ( ( TopOpen ` RRfld )
                                  |`t ( 0 [,) +oo ) )
                                fLimf
                                L
                              )
                              `
                              ( i e. Y |-> ( ( F ` i ) ` x ) )
                            )
                          )
                      }
                    )
                  )
                  ->
                  ( Q1067156XLIntegral M f ) e.
                    (
                      (
                        (
                          ( TopOpen `
                            ( RR*s |`s ( 0 [,] +oo ) ) )
                          fLimf
                          L
                        )
                        `
                        ( i e. Y |->
                          ( Q1067156XLIntegral M ( F ` i ) ) )
                      )
                    )
                )
              )
            )
          )
  $.
$}

${
  $d A B F G H J L M Y c d f i k n r x y $.

  thousand-theorems-q1067156x-sequence-bounded-convergence $a |-
    A. M e. U. ran measures
      A. J e. ( TopOn ` U. dom M )
        A. F A. c A. f
          (
            (
              (
                ( M ` U. dom M ) e. ( 0 [,) +oo )
                /\
                J C_ dom M
              )
              /\
              (
                c e. ( 0 [,) +oo )
                /\
                (
                  F : NN0 --> ( ( 0 [,) +oo ) ^m U. dom M )
                  /\
                  A. n e. NN0
                    ( Q1067156XBoundedContinuous J ( F ` n ) )
                )
              )
            )
            ->
            (
              (
                (
                  f : U. dom M --> ( 0 [,) +oo )
                  /\
                  A. n e. NN0 A. x e. U. dom M
                    ( ( F ` n ) ` x ) <_ c
                )
                /\
                A. x e. U. dom M
                  ( f ` x ) e.
                    (
                      (
                        (
                          ( ( TopOpen ` RRfld )
                            |`t ( 0 [,) +oo ) )
                          fLimf
                          Q1067156XNatAtTop
                        )
                        `
                        ( n e. NN0 |-> ( ( F ` n ) ` x ) )
                      )
                    )
              )
              ->
              ( Q1067156XLIntegral M f ) e.
                (
                  (
                    (
                      ( TopOpen `
                        ( RR*s |`s ( 0 [,] +oo ) ) )
                      fLimf
                      Q1067156XNatAtTop
                    )
                    `
                    ( n e. NN0 |->
                      ( Q1067156XLIntegral M ( F ` n ) ) )
                  )
                )
            )
          )
  $.
$}
