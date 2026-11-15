$(
  Statement-only formalization of Thousand Theorems corpus artifact Q7525341
  (thousand-theorems__metamath__Q7525341), "Sion's minimax theorem": for a
  nonempty compact convex subset X of a real topological vector space, a
  convex subset Y of another real topological vector space, and a payoff into
  an arbitrary linearly ordered codomain whose X-sections are lower
  semicontinuous and quasiconvex and whose Y-sections are upper
  semicontinuous and quasiconcave, explicitly specified iterated infima and
  suprema are equal. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The payoff f is represented on the Cartesian product of the two carriers;
  this is the uncurried form of the source function E -> F -> beta.

  Q7525341LowerSection and Q7525341UpperSection expand the source
  within-set semicontinuity predicates using their equivalent open-
  neighborhood formulations. Q7525341QuasiconvexSection and
  Q7525341QuasiconcaveSection expand the source definitions by requiring all
  sublevel, respectively superlevel, sets to be convex.

  Q7525341IsLUB and Q7525341IsGLB directly encode least-upper-bound and
  greatest-lower-bound predicates, so no completeness assumption is placed
  on the linearly ordered codomain. The final declaration is the single
  unproved corpus $a statement. All preceding $a declarations are syntax or
  faithful definitions, and this database contains no $p proof statement.
$)

$c Q7525341Convex Q7525341LowerSection Q7525341UpperSection
   Q7525341QuasiconvexSection Q7525341QuasiconcaveSection
   Q7525341RowValues Q7525341ColumnValues Q7525341RestrictedRange
   Q7525341IsLUB Q7525341IsGLB $.

q7525341-convex-syntax
  $a wff ( Q7525341Convex E X ) $.
q7525341-lower-section-syntax
  $a wff ( Q7525341LowerSection B E X f y ) $.
q7525341-upper-section-syntax
  $a wff ( Q7525341UpperSection B F Y f x ) $.
q7525341-quasiconvex-section-syntax
  $a wff ( Q7525341QuasiconvexSection B E X f y ) $.
q7525341-quasiconcave-section-syntax
  $a wff ( Q7525341QuasiconcaveSection B F Y f x ) $.
q7525341-row-values-syntax
  $a class ( Q7525341RowValues B f Y x ) $.
q7525341-column-values-syntax
  $a class ( Q7525341ColumnValues B f X y ) $.
q7525341-restricted-range-syntax
  $a class ( Q7525341RestrictedRange B f X ) $.
q7525341-is-lub-syntax
  $a wff ( Q7525341IsLUB B X x ) $.
q7525341-is-glb-syntax
  $a wff ( Q7525341IsGLB B X x ) $.

${
  $d E X t x y $.

  q7525341-convex-definition $a |- (
    ( Q7525341Convex E X )
    <->
    A. x e. X A. y e. X A. t e. ( 0 [,] 1 )
      (
        (
          ( t ( .s ` E ) x )
          ( +g ` E )
          ( ( 1 - t ) ( .s ` E ) y )
        )
        e. X
      )
  ) $.
$}

${
  $d B E O X b f x y z $.

  q7525341-lower-section-definition $a |- (
    ( Q7525341LowerSection B E X f y )
    <->
    A. x e. X A. b e. ( Base ` B )
      (
        b ( lt ` B ) ( f ` <. x , y >. )
        ->
        E. O e. ( TopOpen ` E )
          (
            x e. O
            /\
            A. z e. ( O i^i X )
              b ( lt ` B ) ( f ` <. z , y >. )
          )
      )
  ) $.
$}

${
  $d B F O Y b f x y z $.

  q7525341-upper-section-definition $a |- (
    ( Q7525341UpperSection B F Y f x )
    <->
    A. y e. Y A. b e. ( Base ` B )
      (
        ( f ` <. x , y >. ) ( lt ` B ) b
        ->
        E. O e. ( TopOpen ` F )
          (
            y e. O
            /\
            A. z e. ( O i^i Y )
              ( f ` <. x , z >. ) ( lt ` B ) b
          )
      )
  ) $.
$}

${
  $d B E X b f x y $.

  q7525341-quasiconvex-section-definition $a |- (
    ( Q7525341QuasiconvexSection B E X f y )
    <->
    A. b e. ( Base ` B )
      (
        Q7525341Convex
        E
        { x e. X | ( f ` <. x , y >. ) ( le ` B ) b }
      )
  ) $.
$}

${
  $d B F Y b f x y $.

  q7525341-quasiconcave-section-definition $a |- (
    ( Q7525341QuasiconcaveSection B F Y f x )
    <->
    A. b e. ( Base ` B )
      (
        Q7525341Convex
        F
        { y e. Y | b ( le ` B ) ( f ` <. x , y >. ) }
      )
  ) $.
$}

${
  $d B Y b f x y $.

  q7525341-row-values-definition $a |- (
    Q7525341RowValues B f Y x
  ) = {
    b e. ( Base ` B ) |
      E. y e. Y b = ( f ` <. x , y >. )
  } $.
$}

${
  $d B X b f x y $.

  q7525341-column-values-definition $a |- (
    Q7525341ColumnValues B f X y
  ) = {
    b e. ( Base ` B ) |
      E. x e. X b = ( f ` <. x , y >. )
  } $.
$}

${
  $d B X b f x $.

  q7525341-restricted-range-definition $a |- (
    Q7525341RestrictedRange B f X
  ) = {
    b e. ( Base ` B ) |
      E. x e. X b = ( f ` x )
  } $.
$}

${
  $d B X b x z $.

  q7525341-is-lub-definition $a |- (
    ( Q7525341IsLUB B X x )
    <->
    (
      x e. ( Base ` B )
      /\
      (
        A. b e. X b ( le ` B ) x
        /\
        A. z e. ( Base ` B )
          (
            A. b e. X b ( le ` B ) z
            ->
            x ( le ` B ) z
          )
      )
    )
  ) $.
$}

${
  $d B X b x z $.

  q7525341-is-glb-definition $a |- (
    ( Q7525341IsGLB B X x )
    <->
    (
      x e. ( Base ` B )
      /\
      (
        A. b e. X x ( le ` B ) b
        /\
        A. z e. ( Base ` B )
          (
            A. b e. X z ( le ` B ) b
            ->
            z ( le ` B ) x
          )
      )
    )
  ) $.
$}

${
  $d B E F X Y f i s u v x y $.

  thousand-theorems-q7525341-sion-minimax $a |-
    A. B e. Toset
      A. E e. RRVec
        A. F e. RRVec
          A. X e. ~P ( Base ` E )
            A. Y e. ~P ( Base ` F )
              A. f e.
                ( ( Base ` B ) ^m ( ( Base ` E ) X. ( Base ` F ) ) )
                A. s e. ( ( Base ` B ) ^m ( Base ` E ) )
                  A. u e. ( Base ` B )
                    A. i e. ( ( Base ` B ) ^m ( Base ` F ) )
                      A. v e. ( Base ` B )
                        (
                          (
                            E e. TopMod
                            /\
                            (
                              F e. TopMod
                              /\
                              (
                                X =/= (/) 
                                /\
                                (
                                  ( ( TopOpen ` E ) |`t X ) e. Comp
                                  /\
                                  (
                                    ( Q7525341Convex E X )
                                    /\
                                    (
                                      ( Q7525341Convex F Y )
                                      /\
                                      (
                                        A. y e. Y
                                          (
                                            ( Q7525341LowerSection B E X f y )
                                            /\
                                            ( Q7525341QuasiconvexSection
                                                B E X f y )
                                          )
                                        /\
                                        (
                                          A. x e. X
                                            (
                                              ( Q7525341UpperSection
                                                  B F Y f x )
                                              /\
                                              ( Q7525341QuasiconcaveSection
                                                  B F Y f x )
                                            )
                                          /\
                                          (
                                            A. x e. X
                                              (
                                                Q7525341IsLUB
                                                B
                                                ( Q7525341RowValues B f Y x )
                                                ( s ` x )
                                              )
                                            /\
                                            (
                                              (
                                                Q7525341IsGLB
                                                B
                                                ( Q7525341RestrictedRange
                                                    B s X )
                                                u
                                              )
                                              /\
                                              (
                                                A. y e. Y
                                                  (
                                                    Q7525341IsGLB
                                                    B
                                                    ( Q7525341ColumnValues
                                                        B f X y )
                                                    ( i ` y )
                                                  )
                                                /\
                                                (
                                                  Q7525341IsLUB
                                                  B
                                                  ( Q7525341RestrictedRange
                                                      B i Y )
                                                  v
                                                )
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                          ->
                          u = v
                        )
  $.
$}
