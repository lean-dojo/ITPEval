$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1148215
  (thousand-theorems__metamath__Q1148215), "Mitchell's embedding theorem":
  every abelian category admits a full and faithful functor into modules over
  a ring which preserves finite limits and finite colimits. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  All objects in this encoding are sets. A category, ring, and module-valued
  functor are finite records represented by actual SetMM functions. Their
  fields, morphisms, scalars, vectors, and linear maps therefore use native
  set equality, with the substitutivity and extensionality of SetMM.

  Q1148215Abelian expands the standard small set-coded definition: a
  preadditive category with a zero object, binary biproducts, kernels and
  cokernels, in which every monomorphism is a kernel and every epimorphism is
  a cokernel. Q1148215Functor describes modules over one ring on every source
  object and an additive functorial action on every source morphism.

  Q1148215Linear recognizes every actual function between two module
  carriers which preserves addition and scalar multiplication.
  Q1148215Full quantifies over all sets L, so its implication ranges over
  every such linear function, not over a selected collection of codes.

  For an additive functor between abelian categories, preservation of finite
  limits is equivalent to preservation of kernels, and preservation of finite
  colimits is equivalent to preservation of cokernels. The two preservation
  predicates use these equivalent characterizations in modules: an image of
  a kernel is injective with range the algebraic kernel, and an image of a
  cokernel is surjective with algebraic kernel equal to the preceding image.

  Every declaration before the final one is syntax or a bidirectional
  definition. The final $a declaration is the single unproved corpus
  statement. There is no $p proof statement in this file.
$)

$c Q1148215Obj Q1148215Arr Q1148215Src Q1148215Tgt
   Q1148215Id Q1148215Comp Q1148215Zero Q1148215Add Q1148215Neg $.
$c Q1148215Hom Q1148215Category Q1148215HomAbGroup
   Q1148215Preadditive Q1148215ZeroObject Q1148215Biproduct
   Q1148215Kernel Q1148215Cokernel Q1148215Mono Q1148215Epi
   Q1148215Abelian $.
$c Q1148215Scalars Q1148215RZero Q1148215ROne
   Q1148215RAdd Q1148215RMul Q1148215RNeg Q1148215Ring $.
$c Q1148215Vectors Q1148215VZero Q1148215VAdd
   Q1148215VNeg Q1148215SMul Q1148215FMap $.
$c Q1148215Module Q1148215Linear Q1148215Functor
   Q1148215Additive Q1148215Full Q1148215Faithful
   Q1148215PresFinLim Q1148215PresFinColim $.

q1148215-obj-syntax $a class ( Q1148215Obj C ) $.
q1148215-arr-syntax $a class ( Q1148215Arr C ) $.
q1148215-src-syntax $a class ( Q1148215Src C f ) $.
q1148215-tgt-syntax $a class ( Q1148215Tgt C f ) $.
q1148215-id-syntax $a class ( Q1148215Id C X ) $.
q1148215-comp-syntax $a class ( Q1148215Comp C g f ) $.
q1148215-zero-syntax $a class ( Q1148215Zero C X Y ) $.
q1148215-add-syntax $a class ( Q1148215Add C f g ) $.
q1148215-neg-syntax $a class ( Q1148215Neg C f ) $.

q1148215-hom-syntax $a wff ( Q1148215Hom C f X Y ) $.
q1148215-category-syntax $a wff ( Q1148215Category C ) $.
q1148215-hom-ab-group-syntax
  $a wff ( Q1148215HomAbGroup C X Y ) $.
q1148215-preadditive-syntax $a wff ( Q1148215Preadditive C ) $.
q1148215-zero-object-syntax
  $a wff ( Q1148215ZeroObject C O ) $.
q1148215-biproduct-syntax
  $a wff ( Q1148215Biproduct C X Y B i j p q ) $.
q1148215-kernel-syntax $a wff ( Q1148215Kernel C k f ) $.
q1148215-cokernel-syntax $a wff ( Q1148215Cokernel C q f ) $.
q1148215-mono-syntax $a wff ( Q1148215Mono C f ) $.
q1148215-epi-syntax $a wff ( Q1148215Epi C f ) $.
q1148215-abelian-syntax $a wff ( Q1148215Abelian C ) $.

q1148215-scalars-syntax $a class ( Q1148215Scalars R ) $.
q1148215-rzero-syntax $a class ( Q1148215RZero R ) $.
q1148215-rone-syntax $a class ( Q1148215ROne R ) $.
q1148215-radd-syntax $a class ( Q1148215RAdd R a b ) $.
q1148215-rmul-syntax $a class ( Q1148215RMul R a b ) $.
q1148215-rneg-syntax $a class ( Q1148215RNeg R a ) $.
q1148215-ring-syntax $a wff ( Q1148215Ring R ) $.

q1148215-vectors-syntax $a class ( Q1148215Vectors E X ) $.
q1148215-vzero-syntax $a class ( Q1148215VZero E X ) $.
q1148215-vadd-syntax $a class ( Q1148215VAdd E X u v ) $.
q1148215-vneg-syntax $a class ( Q1148215VNeg E X u ) $.
q1148215-smul-syntax $a class ( Q1148215SMul E X a u ) $.
q1148215-fmap-syntax $a class ( Q1148215FMap E f ) $.

q1148215-module-syntax $a wff ( Q1148215Module E R X ) $.
q1148215-linear-syntax $a wff ( Q1148215Linear E R X Y L ) $.
q1148215-functor-syntax $a wff ( Q1148215Functor C R E ) $.
q1148215-additive-syntax $a wff ( Q1148215Additive C R E ) $.
q1148215-full-syntax $a wff ( Q1148215Full C R E ) $.
q1148215-faithful-syntax $a wff ( Q1148215Faithful C R E ) $.
q1148215-pres-fin-lim-syntax
  $a wff ( Q1148215PresFinLim C R E ) $.
q1148215-pres-fin-colim-syntax
  $a wff ( Q1148215PresFinColim C R E ) $.

q1148215-obj-definition $a
  |- ( Q1148215Obj C ) = ( C ` 0 ) $.
q1148215-arr-definition $a
  |- ( Q1148215Arr C ) = ( C ` 1 ) $.
q1148215-src-definition $a
  |- ( Q1148215Src C f ) = ( ( C ` 2 ) ` f ) $.
q1148215-tgt-definition $a
  |- ( Q1148215Tgt C f ) = ( ( C ` 3 ) ` f ) $.
q1148215-id-definition $a
  |- ( Q1148215Id C X ) = ( ( C ` 4 ) ` X ) $.
q1148215-comp-definition $a
  |- ( Q1148215Comp C g f ) = ( ( C ` 5 ) ` <. g , f >. ) $.
q1148215-zero-definition $a
  |- ( Q1148215Zero C X Y ) = ( ( C ` 6 ) ` <. X , Y >. ) $.
q1148215-add-definition $a
  |- ( Q1148215Add C f g ) = ( ( C ` 7 ) ` <. f , g >. ) $.
q1148215-neg-definition $a
  |- ( Q1148215Neg C f ) = ( ( C ` 8 ) ` f ) $.

q1148215-scalars-definition $a
  |- ( Q1148215Scalars R ) = ( R ` 0 ) $.
q1148215-rzero-definition $a
  |- ( Q1148215RZero R ) = ( R ` 1 ) $.
q1148215-rone-definition $a
  |- ( Q1148215ROne R ) = ( R ` 2 ) $.
q1148215-radd-definition $a
  |- ( Q1148215RAdd R a b ) = ( ( R ` 3 ) ` <. a , b >. ) $.
q1148215-rmul-definition $a
  |- ( Q1148215RMul R a b ) = ( ( R ` 4 ) ` <. a , b >. ) $.
q1148215-rneg-definition $a
  |- ( Q1148215RNeg R a ) = ( ( R ` 5 ) ` a ) $.

q1148215-vectors-definition $a
  |- ( Q1148215Vectors E X ) = ( ( E ` 0 ) ` X ) $.
q1148215-vzero-definition $a
  |- ( Q1148215VZero E X ) = ( ( E ` 1 ) ` X ) $.
q1148215-vadd-definition $a
  |- ( Q1148215VAdd E X u v )
     = ( ( ( E ` 2 ) ` X ) ` <. u , v >. ) $.
q1148215-vneg-definition $a
  |- ( Q1148215VNeg E X u ) = ( ( ( E ` 3 ) ` X ) ` u ) $.
q1148215-smul-definition $a
  |- ( Q1148215SMul E X a u )
     = ( ( ( E ` 4 ) ` X ) ` <. a , u >. ) $.
q1148215-fmap-definition $a
  |- ( Q1148215FMap E f ) = ( ( E ` 5 ) ` f ) $.

${
  $d C X Y f $.

  q1148215-hom-definition $a |- (
    ( Q1148215Hom C f X Y )
    <->
    (
      f e. ( Q1148215Arr C )
      /\
      (
        ( Q1148215Src C f ) = X
        /\
        ( Q1148215Tgt C f ) = Y
      )
    )
  ) $.
$}

${
  $d C W X Y Z f g h $.

  q1148215-category-definition $a |- (
    ( Q1148215Category C )
    <->
    (
      C Fn ( 0 ..^ 9 )
      /\
      (
        ( C ` 2 ) : ( Q1148215Arr C ) --> ( Q1148215Obj C )
        /\
        (
          ( C ` 3 ) : ( Q1148215Arr C ) --> ( Q1148215Obj C )
          /\
          (
            ( C ` 4 ) : ( Q1148215Obj C ) --> ( Q1148215Arr C )
            /\
            ( C ` 5 )
              : ( ( Q1148215Arr C ) X. ( Q1148215Arr C ) )
              --> ( Q1148215Arr C )
          )
        )
      )
      /\
      (
        A. f e. ( Q1148215Arr C )
          (
            Q1148215Hom C f
              ( Q1148215Src C f ) ( Q1148215Tgt C f )
          )
        /\
        (
          A. X e. ( Q1148215Obj C )
            ( Q1148215Hom C ( Q1148215Id C X ) X X )
          /\
          (
            A. X e. ( Q1148215Obj C )
              A. Y e. ( Q1148215Obj C )
                A. Z e. ( Q1148215Obj C )
                  A. f e. ( Q1148215Arr C )
                    A. g e. ( Q1148215Arr C )
                      (
                        (
                          ( Q1148215Hom C f X Y )
                          /\
                          ( Q1148215Hom C g Y Z )
                        )
                        ->
                        (
                          Q1148215Hom C
                            ( Q1148215Comp C g f ) X Z
                        )
                      )
            /\
            (
              A. X e. ( Q1148215Obj C )
                A. Y e. ( Q1148215Obj C )
                  A. f e. ( Q1148215Arr C )
                    (
                      ( Q1148215Hom C f X Y )
                      ->
                      (
                        ( Q1148215Comp C ( Q1148215Id C Y ) f ) = f
                        /\
                        ( Q1148215Comp C f ( Q1148215Id C X ) ) = f
                      )
                    )
              /\
              A. W e. ( Q1148215Obj C )
                A. X e. ( Q1148215Obj C )
                  A. Y e. ( Q1148215Obj C )
                    A. Z e. ( Q1148215Obj C )
                      A. f e. ( Q1148215Arr C )
                        A. g e. ( Q1148215Arr C )
                          A. h e. ( Q1148215Arr C )
                            (
                              (
                                ( Q1148215Hom C f W X )
                                /\
                                (
                                  ( Q1148215Hom C g X Y )
                                  /\
                                  ( Q1148215Hom C h Y Z )
                                )
                              )
                              ->
                              (
                                Q1148215Comp C h
                                  ( Q1148215Comp C g f )
                              )
                              =
                              (
                                Q1148215Comp C
                                  ( Q1148215Comp C h g ) f
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
  $d C X Y f g h $.

  q1148215-hom-ab-group-definition $a |- (
    ( Q1148215HomAbGroup C X Y )
    <->
    (
      ( Q1148215Hom C ( Q1148215Zero C X Y ) X Y )
      /\
      (
        A. f e. ( Q1148215Arr C )
          A. g e. ( Q1148215Arr C )
            (
              (
                ( Q1148215Hom C f X Y )
                /\
                ( Q1148215Hom C g X Y )
              )
              ->
              (
                ( Q1148215Hom C ( Q1148215Add C f g ) X Y )
                /\
                (
                  ( Q1148215Add C f g )
                  =
                  ( Q1148215Add C g f )
                )
              )
            )
        /\
        (
          A. f e. ( Q1148215Arr C )
            (
              ( Q1148215Hom C f X Y )
              ->
              (
                ( Q1148215Hom C ( Q1148215Neg C f ) X Y )
                /\
                (
                  ( Q1148215Add C f ( Q1148215Zero C X Y ) ) = f
                  /\
                  (
                    ( Q1148215Add C f ( Q1148215Neg C f ) )
                    =
                    ( Q1148215Zero C X Y )
                  )
                )
              )
            )
          /\
          A. f e. ( Q1148215Arr C )
            A. g e. ( Q1148215Arr C )
              A. h e. ( Q1148215Arr C )
                (
                  (
                    ( Q1148215Hom C f X Y )
                    /\
                    (
                      ( Q1148215Hom C g X Y )
                      /\
                      ( Q1148215Hom C h X Y )
                    )
                  )
                  ->
                  (
                    Q1148215Add C ( Q1148215Add C f g ) h
                  )
                  =
                  (
                    Q1148215Add C f ( Q1148215Add C g h )
                  )
                )
        )
      )
    )
  ) $.
$}

${
  $d C W X Y Z f g h $.

  q1148215-preadditive-definition $a |- (
    ( Q1148215Preadditive C )
    <->
    (
      ( Q1148215Category C )
      /\
      (
        ( C ` 6 )
          : ( ( Q1148215Obj C ) X. ( Q1148215Obj C ) )
          --> ( Q1148215Arr C )
        /\
        (
          ( C ` 7 )
            : ( ( Q1148215Arr C ) X. ( Q1148215Arr C ) )
            --> ( Q1148215Arr C )
          /\
          ( C ` 8 ) : ( Q1148215Arr C ) --> ( Q1148215Arr C )
        )
      )
      /\
      (
        A. X e. ( Q1148215Obj C )
          A. Y e. ( Q1148215Obj C )
            ( Q1148215HomAbGroup C X Y )
        /\
        (
          A. W e. ( Q1148215Obj C )
            A. X e. ( Q1148215Obj C )
              A. Y e. ( Q1148215Obj C )
                A. f e. ( Q1148215Arr C )
                  A. g e. ( Q1148215Arr C )
                    A. h e. ( Q1148215Arr C )
                      (
                        (
                          ( Q1148215Hom C f W X )
                          /\
                          (
                            ( Q1148215Hom C g X Y )
                            /\
                            ( Q1148215Hom C h X Y )
                          )
                        )
                        ->
                        (
                          Q1148215Comp C
                            ( Q1148215Add C g h ) f
                        )
                        =
                        (
                          Q1148215Add C
                            ( Q1148215Comp C g f )
                            ( Q1148215Comp C h f )
                        )
                      )
          /\
          A. X e. ( Q1148215Obj C )
            A. Y e. ( Q1148215Obj C )
              A. Z e. ( Q1148215Obj C )
                A. f e. ( Q1148215Arr C )
                  A. g e. ( Q1148215Arr C )
                    A. h e. ( Q1148215Arr C )
                      (
                        (
                          ( Q1148215Hom C f X Y )
                          /\
                          (
                            ( Q1148215Hom C g X Y )
                            /\
                            ( Q1148215Hom C h Y Z )
                          )
                        )
                        ->
                        (
                          Q1148215Comp C h
                            ( Q1148215Add C f g )
                        )
                        =
                        (
                          Q1148215Add C
                            ( Q1148215Comp C h f )
                            ( Q1148215Comp C h g )
                        )
                      )
        )
      )
    )
  ) $.
$}

${
  $d C O X f g $.

  q1148215-zero-object-definition $a |- (
    ( Q1148215ZeroObject C O )
    <->
    (
      O e. ( Q1148215Obj C )
      /\
      A. X e. ( Q1148215Obj C )
        (
          E. f e. ( Q1148215Arr C )
            (
              ( Q1148215Hom C f O X )
              /\
              A. g e. ( Q1148215Arr C )
                ( ( Q1148215Hom C g O X ) -> g = f )
            )
          /\
          E. f e. ( Q1148215Arr C )
            (
              ( Q1148215Hom C f X O )
              /\
              A. g e. ( Q1148215Arr C )
                ( ( Q1148215Hom C g X O ) -> g = f )
            )
        )
    )
  ) $.
$}

${
  $d B C X Y i j p q $.

  q1148215-biproduct-definition $a |- (
    ( Q1148215Biproduct C X Y B i j p q )
    <->
    (
      (
        ( X e. ( Q1148215Obj C ) /\ Y e. ( Q1148215Obj C ) )
        /\
        B e. ( Q1148215Obj C )
      )
      /\
      (
        ( Q1148215Hom C i X B )
        /\
        (
          ( Q1148215Hom C j Y B )
          /\
          (
            ( Q1148215Hom C p B X )
            /\
            ( Q1148215Hom C q B Y )
          )
        )
      )
      /\
      (
        ( Q1148215Comp C p i ) = ( Q1148215Id C X )
        /\
        (
          ( Q1148215Comp C q j ) = ( Q1148215Id C Y )
          /\
          (
            ( Q1148215Comp C p j ) = ( Q1148215Zero C Y X )
            /\
            ( Q1148215Comp C q i ) = ( Q1148215Zero C X Y )
          )
        )
      )
      /\
      (
        Q1148215Add C
          ( Q1148215Comp C i p )
          ( Q1148215Comp C j q )
      )
      =
      ( Q1148215Id C B )
    )
  ) $.
$}

${
  $d C T f h k u v $.

  q1148215-kernel-definition $a |- (
    ( Q1148215Kernel C k f )
    <->
    (
      f e. ( Q1148215Arr C )
      /\
      (
        (
          Q1148215Hom C k
            ( Q1148215Src C k ) ( Q1148215Src C f )
        )
        /\
        (
          ( Q1148215Comp C f k )
          =
          (
            Q1148215Zero C
              ( Q1148215Src C k ) ( Q1148215Tgt C f )
          )
        )
      )
      /\
      A. T e. ( Q1148215Obj C )
        A. h e. ( Q1148215Arr C )
          (
            (
              ( Q1148215Hom C h T ( Q1148215Src C f ) )
              /\
              (
                ( Q1148215Comp C f h )
                =
                ( Q1148215Zero C T ( Q1148215Tgt C f ) )
              )
            )
            ->
            E. u e. ( Q1148215Arr C )
              (
                (
                  ( Q1148215Hom C u T ( Q1148215Src C k ) )
                  /\
                  ( Q1148215Comp C k u ) = h
                )
                /\
                A. v e. ( Q1148215Arr C )
                  (
                    (
                      ( Q1148215Hom C v T ( Q1148215Src C k ) )
                      /\
                      ( Q1148215Comp C k v ) = h
                    )
                    ->
                    v = u
                  )
              )
          )
    )
  ) $.
$}

${
  $d C T f h q u v $.

  q1148215-cokernel-definition $a |- (
    ( Q1148215Cokernel C q f )
    <->
    (
      f e. ( Q1148215Arr C )
      /\
      (
        (
          Q1148215Hom C q
            ( Q1148215Tgt C f ) ( Q1148215Tgt C q )
        )
        /\
        (
          ( Q1148215Comp C q f )
          =
          (
            Q1148215Zero C
              ( Q1148215Src C f ) ( Q1148215Tgt C q )
          )
        )
      )
      /\
      A. T e. ( Q1148215Obj C )
        A. h e. ( Q1148215Arr C )
          (
            (
              ( Q1148215Hom C h ( Q1148215Tgt C f ) T )
              /\
              (
                ( Q1148215Comp C h f )
                =
                ( Q1148215Zero C ( Q1148215Src C f ) T )
              )
            )
            ->
            E. u e. ( Q1148215Arr C )
              (
                (
                  ( Q1148215Hom C u ( Q1148215Tgt C q ) T )
                  /\
                  ( Q1148215Comp C u q ) = h
                )
                /\
                A. v e. ( Q1148215Arr C )
                  (
                    (
                      ( Q1148215Hom C v ( Q1148215Tgt C q ) T )
                      /\
                      ( Q1148215Comp C v q ) = h
                    )
                    ->
                    v = u
                  )
              )
          )
    )
  ) $.
$}

${
  $d C T f g h $.

  q1148215-mono-definition $a |- (
    ( Q1148215Mono C f )
    <->
    (
      f e. ( Q1148215Arr C )
      /\
      A. T e. ( Q1148215Obj C )
        A. g e. ( Q1148215Arr C )
          A. h e. ( Q1148215Arr C )
            (
              (
                (
                  ( Q1148215Hom C g T ( Q1148215Src C f ) )
                  /\
                  ( Q1148215Hom C h T ( Q1148215Src C f ) )
                )
                /\
                (
                  ( Q1148215Comp C f g )
                  =
                  ( Q1148215Comp C f h )
                )
              )
              ->
              g = h
            )
    )
  ) $.
$}

${
  $d C T f g h $.

  q1148215-epi-definition $a |- (
    ( Q1148215Epi C f )
    <->
    (
      f e. ( Q1148215Arr C )
      /\
      A. T e. ( Q1148215Obj C )
        A. g e. ( Q1148215Arr C )
          A. h e. ( Q1148215Arr C )
            (
              (
                (
                  ( Q1148215Hom C g ( Q1148215Tgt C f ) T )
                  /\
                  ( Q1148215Hom C h ( Q1148215Tgt C f ) T )
                )
                /\
                (
                  ( Q1148215Comp C g f )
                  =
                  ( Q1148215Comp C h f )
                )
              )
              ->
              g = h
            )
    )
  ) $.
$}

${
  $d B C O X Y f i j k p q $.

  q1148215-abelian-definition $a |- (
    ( Q1148215Abelian C )
    <->
    (
      ( Q1148215Preadditive C )
      /\
      (
        E. O ( Q1148215ZeroObject C O )
        /\
        (
          A. X e. ( Q1148215Obj C )
            A. Y e. ( Q1148215Obj C )
              E. B E. i E. j E. p E. q
                ( Q1148215Biproduct C X Y B i j p q )
          /\
          (
            A. f e. ( Q1148215Arr C )
              (
                E. k e. ( Q1148215Arr C )
                  ( Q1148215Kernel C k f )
                /\
                E. q e. ( Q1148215Arr C )
                  ( Q1148215Cokernel C q f )
              )
            /\
            A. f e. ( Q1148215Arr C )
              (
                (
                  ( Q1148215Mono C f )
                  ->
                  E. q e. ( Q1148215Arr C )
                    ( Q1148215Kernel C f q )
                )
                /\
                (
                  ( Q1148215Epi C f )
                  ->
                  E. k e. ( Q1148215Arr C )
                    ( Q1148215Cokernel C f k )
                )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d R a b c $.

  q1148215-ring-definition $a |- (
    ( Q1148215Ring R )
    <->
    (
      R Fn ( 0 ..^ 6 )
      /\
      (
        ( Q1148215RZero R ) e. ( Q1148215Scalars R )
        /\
        ( Q1148215ROne R ) e. ( Q1148215Scalars R )
      )
      /\
      (
        ( R ` 3 )
          : ( ( Q1148215Scalars R ) X. ( Q1148215Scalars R ) )
          --> ( Q1148215Scalars R )
        /\
        (
          ( R ` 4 )
            : ( ( Q1148215Scalars R ) X. ( Q1148215Scalars R ) )
            --> ( Q1148215Scalars R )
          /\
          ( R ` 5 )
            : ( Q1148215Scalars R ) --> ( Q1148215Scalars R )
        )
      )
      /\
      A. a e. ( Q1148215Scalars R )
        A. b e. ( Q1148215Scalars R )
          A. c e. ( Q1148215Scalars R )
            (
              (
                ( Q1148215RAdd R a b ) = ( Q1148215RAdd R b a )
                /\
                (
                  Q1148215RAdd R ( Q1148215RAdd R a b ) c
                )
                =
                (
                  Q1148215RAdd R a ( Q1148215RAdd R b c )
                )
              )
              /\
              (
                ( Q1148215RAdd R a ( Q1148215RZero R ) ) = a
                /\
                (
                  Q1148215RAdd R a ( Q1148215RNeg R a )
                )
                =
                ( Q1148215RZero R )
              )
              /\
              (
                (
                  Q1148215RMul R ( Q1148215RMul R a b ) c
                )
                =
                (
                  Q1148215RMul R a ( Q1148215RMul R b c )
                )
                /\
                (
                  ( Q1148215RMul R ( Q1148215ROne R ) a ) = a
                  /\
                  ( Q1148215RMul R a ( Q1148215ROne R ) ) = a
                )
              )
              /\
              (
                (
                  Q1148215RMul R a ( Q1148215RAdd R b c )
                )
                =
                (
                  Q1148215RAdd R
                    ( Q1148215RMul R a b )
                    ( Q1148215RMul R a c )
                )
                /\
                (
                  Q1148215RMul R ( Q1148215RAdd R a b ) c
                )
                =
                (
                  Q1148215RAdd R
                    ( Q1148215RMul R a c )
                    ( Q1148215RMul R b c )
                )
              )
            )
    )
  ) $.
$}

${
  $d E R X a b u v w $.

  q1148215-module-definition $a |- (
    ( Q1148215Module E R X )
    <->
    (
      ( Q1148215VZero E X ) e. ( Q1148215Vectors E X )
      /\
      (
        ( ( E ` 2 ) ` X )
          : ( ( Q1148215Vectors E X ) X. ( Q1148215Vectors E X ) )
          --> ( Q1148215Vectors E X )
        /\
        (
          ( ( E ` 3 ) ` X )
            : ( Q1148215Vectors E X ) --> ( Q1148215Vectors E X )
          /\
          ( ( E ` 4 ) ` X )
            : ( ( Q1148215Scalars R ) X. ( Q1148215Vectors E X ) )
            --> ( Q1148215Vectors E X )
        )
      )
      /\
      A. u e. ( Q1148215Vectors E X )
        A. v e. ( Q1148215Vectors E X )
          A. w e. ( Q1148215Vectors E X )
            (
              (
                ( Q1148215VAdd E X u v ) = ( Q1148215VAdd E X v u )
                /\
                (
                  Q1148215VAdd E X ( Q1148215VAdd E X u v ) w
                )
                =
                (
                  Q1148215VAdd E X u ( Q1148215VAdd E X v w )
                )
              )
              /\
              (
                ( Q1148215VAdd E X u ( Q1148215VZero E X ) ) = u
                /\
                (
                  Q1148215VAdd E X u ( Q1148215VNeg E X u )
                )
                =
                ( Q1148215VZero E X )
              )
              /\
              A. a e. ( Q1148215Scalars R )
                A. b e. ( Q1148215Scalars R )
                  (
                    (
                      Q1148215SMul E X
                        ( Q1148215RAdd R a b ) u
                    )
                    =
                    (
                      Q1148215VAdd E X
                        ( Q1148215SMul E X a u )
                        ( Q1148215SMul E X b u )
                    )
                    /\
                    (
                      Q1148215SMul E X a
                        ( Q1148215VAdd E X u v )
                    )
                    =
                    (
                      Q1148215VAdd E X
                        ( Q1148215SMul E X a u )
                        ( Q1148215SMul E X a v )
                    )
                    /\
                    (
                      Q1148215SMul E X
                        ( Q1148215RMul R a b ) u
                    )
                    =
                    (
                      Q1148215SMul E X a
                        ( Q1148215SMul E X b u )
                    )
                    /\
                    (
                      ( Q1148215SMul E X ( Q1148215ROne R ) u ) = u
                      /\
                      (
                        Q1148215SMul E X ( Q1148215RZero R ) u
                      )
                      =
                      ( Q1148215VZero E X )
                    )
                  )
            )
    )
  ) $.
$}

${
  $d E L R X Y a u v $.

  q1148215-linear-definition $a |- (
    ( Q1148215Linear E R X Y L )
    <->
    (
      L : ( Q1148215Vectors E X ) --> ( Q1148215Vectors E Y )
      /\
      (
        ( L ` ( Q1148215VZero E X ) ) = ( Q1148215VZero E Y )
        /\
        A. u e. ( Q1148215Vectors E X )
          A. v e. ( Q1148215Vectors E X )
            A. a e. ( Q1148215Scalars R )
              (
                (
                  L ` ( Q1148215VAdd E X u v )
                )
                =
                (
                  Q1148215VAdd E Y ( L ` u ) ( L ` v )
                )
                /\
                (
                  L ` ( Q1148215SMul E X a u )
                )
                =
                (
                  Q1148215SMul E Y a ( L ` u )
                )
              )
      )
    )
  ) $.
$}

${
  $d C E R W X Y Z f g u $.

  q1148215-functor-definition $a |- (
    ( Q1148215Functor C R E )
    <->
    (
      (
        ( Q1148215Category C )
        /\
        ( Q1148215Ring R )
      )
      /\
      (
        E Fn ( 0 ..^ 6 )
        /\
        (
          ( E ` 0 ) Fn ( Q1148215Obj C )
          /\
          (
            ( E ` 1 ) Fn ( Q1148215Obj C )
            /\
            (
              ( E ` 2 ) Fn ( Q1148215Obj C )
              /\
              (
                ( E ` 3 ) Fn ( Q1148215Obj C )
                /\
                (
                  ( E ` 4 ) Fn ( Q1148215Obj C )
                  /\
                  ( E ` 5 ) Fn ( Q1148215Arr C )
                )
              )
            )
          )
        )
      )
      /\
      (
        A. X e. ( Q1148215Obj C )
          ( Q1148215Module E R X )
        /\
        A. f e. ( Q1148215Arr C )
          (
            Q1148215Linear E R
              ( Q1148215Src C f ) ( Q1148215Tgt C f )
              ( Q1148215FMap E f )
          )
      )
      /\
      (
        A. X e. ( Q1148215Obj C )
          (
            ( Q1148215FMap E ( Q1148215Id C X ) )
            =
            ( u e. ( Q1148215Vectors E X ) |-> u )
          )
        /\
        A. W e. ( Q1148215Obj C )
          A. X e. ( Q1148215Obj C )
            A. Y e. ( Q1148215Obj C )
              A. f e. ( Q1148215Arr C )
                A. g e. ( Q1148215Arr C )
                  (
                    (
                      ( Q1148215Hom C f W X )
                      /\
                      ( Q1148215Hom C g X Y )
                    )
                    ->
                    (
                      Q1148215FMap E ( Q1148215Comp C g f )
                    )
                    =
                    (
                      ( Q1148215FMap E g )
                      o.
                      ( Q1148215FMap E f )
                    )
                  )
      )
    )
  ) $.
$}

${
  $d C E R X Y f g u $.

  q1148215-additive-definition $a |- (
    ( Q1148215Additive C R E )
    <->
    (
      ( Q1148215Functor C R E )
      /\
      A. X e. ( Q1148215Obj C )
        A. Y e. ( Q1148215Obj C )
          (
            (
              Q1148215FMap E ( Q1148215Zero C X Y )
            )
            =
            (
              u e. ( Q1148215Vectors E X )
              |->
              ( Q1148215VZero E Y )
            )
            /\
            A. f e. ( Q1148215Arr C )
              A. g e. ( Q1148215Arr C )
                (
                  (
                    ( Q1148215Hom C f X Y )
                    /\
                    ( Q1148215Hom C g X Y )
                  )
                  ->
                  (
                    Q1148215FMap E ( Q1148215Add C f g )
                  )
                  =
                  (
                    u e. ( Q1148215Vectors E X )
                    |->
                    (
                      Q1148215VAdd E Y
                        ( ( Q1148215FMap E f ) ` u )
                        ( ( Q1148215FMap E g ) ` u )
                    )
                  )
                )
          )
    )
  ) $.
$}

${
  $d C E L R X Y f $.

  q1148215-full-definition $a |- (
    ( Q1148215Full C R E )
    <->
    A. X e. ( Q1148215Obj C )
      A. Y e. ( Q1148215Obj C )
        A. L
          (
            ( Q1148215Linear E R X Y L )
            ->
            E. f e. ( Q1148215Arr C )
              (
                ( Q1148215Hom C f X Y )
                /\
                ( Q1148215FMap E f ) = L
              )
          )
  ) $.
$}

${
  $d C E R X Y f g $.

  q1148215-faithful-definition $a |- (
    ( Q1148215Faithful C R E )
    <->
    A. X e. ( Q1148215Obj C )
      A. Y e. ( Q1148215Obj C )
        A. f e. ( Q1148215Arr C )
          A. g e. ( Q1148215Arr C )
            (
              (
                (
                  ( Q1148215Hom C f X Y )
                  /\
                  ( Q1148215Hom C g X Y )
                )
                /\
                ( Q1148215FMap E f ) = ( Q1148215FMap E g )
              )
              ->
              f = g
            )
  ) $.
$}

${
  $d C E R f k u $.

  q1148215-pres-fin-lim-definition $a |- (
    ( Q1148215PresFinLim C R E )
    <->
    (
      ( Q1148215Additive C R E )
      /\
      A. f e. ( Q1148215Arr C )
        A. k e. ( Q1148215Arr C )
          (
            ( Q1148215Kernel C k f )
            ->
            (
              ( Q1148215FMap E k )
                : ( Q1148215Vectors E ( Q1148215Src C k ) )
                -1-1->
                ( Q1148215Vectors E ( Q1148215Src C f ) )
              /\
              ran ( Q1148215FMap E k )
              =
              {
                u e. ( Q1148215Vectors E ( Q1148215Src C f ) )
                |
                (
                  ( Q1148215FMap E f ) ` u
                )
                =
                ( Q1148215VZero E ( Q1148215Tgt C f ) )
              }
            )
          )
    )
  ) $.
$}

${
  $d C E R f q u $.

  q1148215-pres-fin-colim-definition $a |- (
    ( Q1148215PresFinColim C R E )
    <->
    (
      ( Q1148215Additive C R E )
      /\
      A. f e. ( Q1148215Arr C )
        A. q e. ( Q1148215Arr C )
          (
            ( Q1148215Cokernel C q f )
            ->
            (
              ( Q1148215FMap E q )
                : ( Q1148215Vectors E ( Q1148215Tgt C f ) )
                -onto->
                ( Q1148215Vectors E ( Q1148215Tgt C q ) )
              /\
              {
                u e. ( Q1148215Vectors E ( Q1148215Tgt C f ) )
                |
                (
                  ( Q1148215FMap E q ) ` u
                )
                =
                ( Q1148215VZero E ( Q1148215Tgt C q ) )
              }
              =
              (
                ( Q1148215FMap E f )
                "
                ( Q1148215Vectors E ( Q1148215Src C f ) )
              )
            )
          )
    )
  ) $.
$}

${
  $d C E R $.

  q1148215-mitchell-embedding-theorem $a |- A. C
    (
      ( Q1148215Abelian C )
      ->
      E. R E. E
        (
          ( Q1148215Functor C R E )
          /\
          (
            ( Q1148215Full C R E )
            /\
            (
              ( Q1148215Faithful C R E )
              /\
              (
                ( Q1148215PresFinLim C R E )
                /\
                ( Q1148215PresFinColim C R E )
              )
            )
          )
        )
    ) $.
$}
