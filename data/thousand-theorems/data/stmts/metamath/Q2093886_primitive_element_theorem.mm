$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2093886
  (thousand-theorems__metamath__Q2093886), "Primitive element theorem":
  every finite-dimensional separable extension of fields has an element
  generating the entire extension field over the base field. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A is an arbitrary field homomorphism from F to E, representing the algebra
  structure in the source theorem. Q2093886ExtensionModule is E as an
  F-vector space, with scalar action c . x = A(c) * x.

  Q2093886MapPolynomial maps polynomial coefficients along A.
  Q2093886FiniteDimensional says that the resulting vector space has a finite
  basis. Q2093886Separable says that every element of E is annihilated by a
  nonzero polynomial over F which is coprime to its formal derivative. Over a
  field this is equivalent to every element being separable over F.

  Q2093886Generates says that every element of E is a quotient of values at a
  of two F-polynomials, with nonzero denominator. This is equivalent to the
  simple intermediate field F(a) being all of E. Every declaration below is
  an unproved $a statement encoding; this database contains no $p proof.
$)

$c Q2093886ExtensionModule Q2093886MapPolynomial
   Q2093886FiniteDimensional Q2093886Separable Q2093886Generates $.

q2093886-extension-module-syntax
  $a class ( Q2093886ExtensionModule F E A ) $.
q2093886-map-polynomial-syntax
  $a wff ( Q2093886MapPolynomial F E A P Q ) $.
q2093886-finite-dimensional-syntax
  $a wff ( Q2093886FiniteDimensional F E A ) $.
q2093886-separable-syntax
  $a wff ( Q2093886Separable F E A ) $.
q2093886-generates-syntax
  $a wff ( Q2093886Generates F E A a ) $.

${
  $d A E F a x $.

  q2093886-extension-module-definition $a |- (
    Q2093886ExtensionModule F E A
  ) = (
    {
      <.
        ( Base ` ndx ) ,
        ( Base ` E )
      >. ,
      <.
        ( +g ` ndx ) ,
        ( +g ` E )
      >. ,
      <.
        ( Scalar ` ndx ) ,
        F
      >.
    }
    u.
    {
      <.
        ( .s ` ndx ) ,
        (
          a e. ( Base ` F ) ,
          x e. ( Base ` E )
          |->
          ( ( A ` a ) ( .r ` E ) x )
        )
      >.
    }
  ) $.
$}

${
  $d A E F P Q k $.

  q2093886-map-polynomial-definition $a |- (
    Q2093886MapPolynomial F E A P Q
  ) <->
  (
    P e. ( Base ` ( Poly1 ` F ) )
    /\
    (
      Q e. ( Base ` ( Poly1 ` E ) )
      /\
      A. k e. NN0
        (
          ( ( coe1 ` Q ) ` k )
          =
          ( A ` ( ( coe1 ` P ) ` k ) )
        )
    )
  ) $.
$}

${
  $d A E F b $.

  q2093886-finite-dimensional-definition $a |- (
    Q2093886FiniteDimensional F E A
  ) <->
  (
    E. b e. (
      LBasis ` ( Q2093886ExtensionModule F E A )
    )
      b e. Fin
  ) $.
$}

${
  $d A E F P Q U V x $.

  q2093886-separable-definition $a |- (
    Q2093886Separable F E A
  ) <->
  (
    A. x e. ( Base ` E )
      E. P e. ( Base ` ( Poly1 ` F ) )
        (
          P =/= ( 0g ` ( Poly1 ` F ) )
          /\
          E. Q e. ( Base ` ( Poly1 ` E ) )
            (
              ( Q2093886MapPolynomial F E A P Q )
              /\
              (
                ( ( ( eval1 ` E ) ` Q ) ` x )
                =
                ( 0g ` E )
                /\
                E. U e. ( Base ` ( Poly1 ` F ) )
                  E. V e. ( Base ` ( Poly1 ` F ) )
                    (
                      (
                        U
                        ( .r ` ( Poly1 ` F ) )
                        P
                      )
                      ( +g ` ( Poly1 ` F ) )
                      (
                        V
                        ( .r ` ( Poly1 ` F ) )
                        (
                          ( ( ( 1o mPSDer F ) ` (/) ) ` P )
                        )
                      )
                    )
                    =
                    ( 1r ` ( Poly1 ` F ) )
              )
            )
        )
  ) $.
$}

${
  $d A E F P Q R S a x $.

  q2093886-generates-definition $a |- (
    Q2093886Generates F E A a
  ) <->
  (
    a e. ( Base ` E )
    /\
    A. x e. ( Base ` E )
      E. P e. ( Base ` ( Poly1 ` F ) )
        E. Q e. ( Base ` ( Poly1 ` F ) )
          E. R e. ( Base ` ( Poly1 ` E ) )
            E. S e. ( Base ` ( Poly1 ` E ) )
              (
                ( Q2093886MapPolynomial F E A P R )
                /\
                (
                  ( Q2093886MapPolynomial F E A Q S )
                  /\
                  (
                    ( ( ( eval1 ` E ) ` S ) ` a )
                    =/=
                    ( 0g ` E )
                    /\
                    x
                    =
                    (
                      ( ( ( eval1 ` E ) ` R ) ` a )
                      ( /r ` E )
                      ( ( ( eval1 ` E ) ` S ) ` a )
                    )
                  )
                )
              )
  ) $.
$}

${
  $d A E F a $.

  thousand-theorems-q2093886-primitive-element-theorem $a |-
    A. F e. Field
      A. E e. Field
        A. A e. ( F RingHom E )
          (
            (
              ( Q2093886FiniteDimensional F E A )
              /\
              ( Q2093886Separable F E A )
            )
            ->
            E. a e. ( Base ` E )
              ( Q2093886Generates F E A a )
          )
  $.
$}
