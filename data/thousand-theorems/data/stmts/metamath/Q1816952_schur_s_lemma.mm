$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1816952
  (thousand-theorems__metamath__Q1816952), "Schur's lemma": in an
  algebraically closed-field-linear preadditive category with kernels, the
  finite-dimensional endomorphism space of a simple object has dimension one.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The category C is a native SetMM category. Z, P, and T encode respectively
  its zero morphisms, addition on hom-sets, and scalar multiplication by K.
  Q1816952HomSpace packages each actual hom-set as a SetMM left vector space.
  Q1816952LinearPreadditive requires all these vector-space laws and bilinearity
  of composition, so it is exactly the combined preadditive and K-linear
  structure used by the Lean source.

  Q1816952HasKernels expands the usual universal property for every morphism.
  Q1816952Simple is Mathlib's definition: every monomorphism into X is an
  isomorphism exactly when it is nonzero. Q1816952FiniteDimensional says that
  the actual endomorphism vector space has a finite basis. Q1816952AlgClosed
  is the usual nonconstant-polynomial root property over a SetMM field.

  Every declaration before the final assertion is syntax or a bidirectional
  definition. The final $a assertion is the single unproved corpus statement;
  this database contains no $p proof statement.
$)

$c Q1816952Zero Q1816952Add Q1816952SMul Q1816952Comp $.
$c Q1816952HomSpace Q1816952LinearPreadditive Q1816952Kernel
   Q1816952HasKernels Q1816952Simple Q1816952FiniteDimensional
   Q1816952AlgClosed $.

q1816952-zero-syntax $a class ( Q1816952Zero Z X Y ) $.
q1816952-add-syntax $a class ( Q1816952Add P X Y f g ) $.
q1816952-smul-syntax $a class ( Q1816952SMul T X Y a f ) $.
q1816952-comp-syntax $a class ( Q1816952Comp C X Y W g f ) $.
q1816952-hom-space-syntax
  $a class ( Q1816952HomSpace K C P T X Y ) $.

q1816952-linear-preadditive-syntax
  $a wff ( Q1816952LinearPreadditive K C Z P T ) $.
q1816952-kernel-syntax
  $a wff ( Q1816952Kernel C Z K k X Y f ) $.
q1816952-has-kernels-syntax
  $a wff ( Q1816952HasKernels C Z ) $.
q1816952-simple-syntax
  $a wff ( Q1816952Simple C Z X ) $.
q1816952-finite-dimensional-syntax
  $a wff ( Q1816952FiniteDimensional K C P T X Y ) $.
q1816952-algebraically-closed-syntax
  $a wff ( Q1816952AlgClosed K ) $.

q1816952-zero-definition $a |- (
  Q1816952Zero Z X Y
) = ( Z ` <. X , Y >. ) $.

q1816952-add-definition $a |- (
  Q1816952Add P X Y f g
) = ( P ` <. <. X , Y >. , <. f , g >. >. ) $.

q1816952-smul-definition $a |- (
  Q1816952SMul T X Y a f
) = ( T ` <. <. X , Y >. , <. a , f >. >. ) $.

q1816952-comp-definition $a |- (
  Q1816952Comp C X Y W g f
) = ( g ( <. X , Y >. ( comp ` C ) W ) f ) $.

${
  $d C K P T X Y a f g $.

  q1816952-hom-space-definition $a |- (
    Q1816952HomSpace K C P T X Y
  ) = (
    {
      <.
        ( Base ` ndx ) ,
        ( X ( Hom ` C ) Y )
      >. ,
      <.
        ( +g ` ndx ) ,
        (
          f e. ( X ( Hom ` C ) Y ) ,
          g e. ( X ( Hom ` C ) Y )
          |->
          ( Q1816952Add P X Y f g )
        )
      >. ,
      <.
        ( Scalar ` ndx ) ,
        K
      >.
    }
    u.
    {
      <.
        ( .s ` ndx ) ,
        (
          a e. ( Base ` K ) ,
          f e. ( X ( Hom ` C ) Y )
          |->
          ( Q1816952SMul T X Y a f )
        )
      >.
    }
  ) $.
$}

${
  $d C K P T W X Y Z a f g h i $.

  q1816952-linear-preadditive-definition $a |- (
    Q1816952LinearPreadditive K C Z P T
  ) <->
  (
    K e. Field
    /\
    (
      C e. Cat
      /\
      (
        A. X e. ( Base ` C )
          A. Y e. ( Base ` C )
            (
              (
                Q1816952HomSpace K C P T X Y
              ) e. LVec
              /\
              (
                Q1816952Zero Z X Y
              ) = (
                0g ` ( Q1816952HomSpace K C P T X Y )
              )
            )
        /\
        A. W e. ( Base ` C )
          A. X e. ( Base ` C )
            A. Y e. ( Base ` C )
              A. f e. ( W ( Hom ` C ) X )
                A. g e. ( W ( Hom ` C ) X )
                  A. h e. ( X ( Hom ` C ) Y )
                    A. i e. ( X ( Hom ` C ) Y )
                      A. a e. ( Base ` K )
                        (
                          (
                            Q1816952Comp C W X Y h
                              ( Q1816952Add P W X f g )
                          )
                          =
                          (
                            Q1816952Add P W Y
                              ( Q1816952Comp C W X Y h f )
                              ( Q1816952Comp C W X Y h g )
                          )
                          /\
                          (
                            (
                              Q1816952Comp C W X Y
                                ( Q1816952Add P X Y h i ) f
                            )
                            =
                            (
                              Q1816952Add P W Y
                                ( Q1816952Comp C W X Y h f )
                                ( Q1816952Comp C W X Y i f )
                            )
                            /\
                            (
                              (
                                Q1816952Comp C W X Y h
                                  ( Q1816952SMul T W X a f )
                              )
                              =
                              (
                                Q1816952SMul T W Y a
                                  ( Q1816952Comp C W X Y h f )
                              )
                              /\
                              (
                                Q1816952Comp C W X Y
                                  ( Q1816952SMul T X Y a h ) f
                              )
                              =
                              (
                                Q1816952SMul T W Y a
                                  ( Q1816952Comp C W X Y h f )
                              )
                            )
                          )
                        )
      )
    )
  ) $.
$}

${
  $d C K T X Y Z f h k u v $.

  q1816952-kernel-definition $a |- (
    Q1816952Kernel C Z K k X Y f
  ) <->
  (
    (
      K e. ( Base ` C )
      /\
      (
        f e. ( X ( Hom ` C ) Y )
        /\
        k e. ( K ( Hom ` C ) X )
      )
    )
    /\
    (
      (
        Q1816952Comp C K X Y f k
      ) = (
        Q1816952Zero Z K Y
      )
      /\
      A. T e. ( Base ` C )
        A. h e. ( T ( Hom ` C ) X )
          (
            (
              Q1816952Comp C T X Y f h
            ) = (
              Q1816952Zero Z T Y
            )
            ->
            E. u e. ( T ( Hom ` C ) K )
              (
                (
                  Q1816952Comp C T K X k u
                ) = h
                /\
                A. v e. ( T ( Hom ` C ) K )
                  (
                    (
                      Q1816952Comp C T K X k v
                    ) = h
                    ->
                    v = u
                  )
              )
          )
    )
  ) $.
$}

${
  $d C K X Y Z f k $.

  q1816952-has-kernels-definition $a |- (
    Q1816952HasKernels C Z
  ) <->
  (
    C e. Cat
    /\
    A. X e. ( Base ` C )
      A. Y e. ( Base ` C )
        A. f e. ( X ( Hom ` C ) Y )
          E. K e. ( Base ` C )
            E. k e. ( K ( Hom ` C ) X )
              ( Q1816952Kernel C Z K k X Y f )
  ) $.
$}

${
  $d C X Y Z f $.

  q1816952-simple-definition $a |- (
    Q1816952Simple C Z X
  ) <->
  (
    X e. ( Base ` C )
    /\
    A. Y e. ( Base ` C )
      A. f e. ( Y ( Hom ` C ) X )
        (
          f e. ( Y ( Mono ` C ) X )
          ->
          (
            f e. ( Y ( Iso ` C ) X )
            <->
            f =/= ( Q1816952Zero Z Y X )
          )
        )
  ) $.
$}

${
  $d C K P T X Y b $.

  q1816952-finite-dimensional-definition $a |- (
    Q1816952FiniteDimensional K C P T X Y
  ) <->
  (
    E. b e. (
      LBasis ` ( Q1816952HomSpace K C P T X Y )
    )
      b e. Fin
  ) $.
$}

${
  $d K c p x $.

  q1816952-algebraically-closed-definition $a |- (
    Q1816952AlgClosed K
  ) <->
  (
    K e. Field
    /\
    A. p e. ( Base ` ( 1o mPoly K ) )
      (
        A. c e. ( Base ` K )
          p =/= ( ( algSc ` ( 1o mPoly K ) ) ` c )
        ->
        E. x e. ( Base ` K )
          ( ( ( eval1 ` K ) ` p ) ` x ) = ( 0g ` K )
      )
  ) $.
$}

${
  $d C K P T X Z $.

  thousand-theorems-q1816952-schur-lemma $a |-
    A. K A. C A. Z A. P A. T A. X
      (
        (
          Q1816952AlgClosed K
          /\
          (
            Q1816952LinearPreadditive K C Z P T
            /\
            (
              Q1816952HasKernels C Z
              /\
              (
                Q1816952Simple C Z X
                /\
                Q1816952FiniteDimensional K C P T X X
              )
            )
          )
        )
        ->
        (
          dim ` ( Q1816952HomSpace K C P T X X )
        ) = 1
      )
  $.
$}
