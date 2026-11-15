$(
  Statement-only formalization of Thousand Theorems corpus artifact Q20971632
  (thousand-theorems__metamath__Q20971632), "Lie's theorem": every nonzero
  finite-dimensional triangularizable module over a solvable Lie algebra
  over an arbitrary characteristic-zero field has a nonzero common weight
  vector for some linear functional on the Lie algebra. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Q20971632LieAlgebra K L B expands the additive, scalar-bilinear,
  alternating, and Jacobi laws for the bracket B on the K-vector space L.
  Q20971632LieModule K L V B A similarly expands the bilinear Lie action A
  and its representation identity.

  Q20971632Solvable L B says that the derived series, formed by taking the
  linear span of all brackets at each successor stage, reaches the zero
  subspace after finitely many stages. Q20971632GenEigen V A x c v says that
  v is killed by a finite power of the operator A(x,-)-c. The
  Q20971632Triangularizable condition requires every vector, for every x, to
  be a finite sum of such generalized eigenvectors (with possibly different
  eigenvalues). This is the elementwise form of the source condition that
  the supremum of all maximal generalized eigenspaces is the whole module.

  Finite dimensionality is existence of a finite SetMM linear basis. In the
  conclusion, f is a SetMM linear map L -> K and the nonzero vector v lies in
  its common weight space. Thus the conclusion is equivalent to existence of
  a linear functional whose weight space is nontrivial.

  The final $a declaration is the single unproved corpus statement. All
  preceding $a declarations are syntax or faithful bidirectional
  definitions, and this database contains no $p proof statement.
$)

$c Q20971632LieAlgebra Q20971632LieModule Q20971632FiniteDimensional
   Q20971632Solvable Q20971632GenEigen Q20971632Triangularizable $.

q20971632-lie-algebra-syntax
  $a wff ( Q20971632LieAlgebra K L B ) $.
q20971632-lie-module-syntax
  $a wff ( Q20971632LieModule K L V B A ) $.
q20971632-finite-dimensional-syntax
  $a wff ( Q20971632FiniteDimensional V ) $.
q20971632-solvable-syntax
  $a wff ( Q20971632Solvable L B ) $.
q20971632-generalized-eigenvector-syntax
  $a wff ( Q20971632GenEigen V A x c v ) $.
q20971632-triangularizable-syntax
  $a wff ( Q20971632Triangularizable K L V A ) $.

${
  $d A B K L V a x y z $.

  q20971632-lie-algebra-definition $a |- (
    ( Q20971632LieAlgebra K L B )
    <->
    (
      K e. Field
      /\
      L e. LVec
      /\
      ( Scalar ` L ) = K
      /\
      B : ( ( Base ` L ) X. ( Base ` L ) ) --> ( Base ` L )
      /\
      A. x e. ( Base ` L )
        A. y e. ( Base ` L )
          A. z e. ( Base ` L )
            A. a e. ( Base ` K )
              (
                (
                  B ` <. ( x ( +g ` L ) y ) , z >.
                )
                =
                (
                  ( B ` <. x , z >. )
                  ( +g ` L )
                  ( B ` <. y , z >. )
                )
                /\
                (
                  B ` <. x , ( y ( +g ` L ) z ) >.
                )
                =
                (
                  ( B ` <. x , y >. )
                  ( +g ` L )
                  ( B ` <. x , z >. )
                )
                /\
                (
                  B ` <. ( a ( .s ` L ) x ) , y >.
                )
                =
                (
                  a
                  ( .s ` L )
                  ( B ` <. x , y >. )
                )
                /\
                (
                  B ` <. x , ( a ( .s ` L ) y ) >.
                )
                =
                (
                  a
                  ( .s ` L )
                  ( B ` <. x , y >. )
                )
                /\
                ( B ` <. x , x >. ) = ( 0g ` L )
                /\
                (
                  B ` <. x , ( B ` <. y , z >. ) >.
                )
                =
                (
                  ( B ` <. ( B ` <. x , y >. ) , z >. )
                  ( +g ` L )
                  ( B ` <. y , ( B ` <. x , z >. ) >. )
                )
              )
    )
  ) $.
$}

${
  $d A B K L V a v w x y $.

  q20971632-lie-module-definition $a |- (
    ( Q20971632LieModule K L V B A )
    <->
    (
      V e. LVec
      /\
      ( Scalar ` V ) = K
      /\
      A : ( ( Base ` L ) X. ( Base ` V ) ) --> ( Base ` V )
      /\
      A. x e. ( Base ` L )
        A. y e. ( Base ` L )
          A. v e. ( Base ` V )
            A. w e. ( Base ` V )
              A. a e. ( Base ` K )
                (
                  (
                    A ` <. ( x ( +g ` L ) y ) , v >.
                  )
                  =
                  (
                    ( A ` <. x , v >. )
                    ( +g ` V )
                    ( A ` <. y , v >. )
                  )
                  /\
                  (
                    A ` <. x , ( v ( +g ` V ) w ) >.
                  )
                  =
                  (
                    ( A ` <. x , v >. )
                    ( +g ` V )
                    ( A ` <. x , w >. )
                  )
                  /\
                  (
                    A ` <. ( a ( .s ` L ) x ) , v >.
                  )
                  =
                  (
                    a
                    ( .s ` V )
                    ( A ` <. x , v >. )
                  )
                  /\
                  (
                    A ` <. x , ( a ( .s ` V ) v ) >.
                  )
                  =
                  (
                    a
                    ( .s ` V )
                    ( A ` <. x , v >. )
                  )
                  /\
                  (
                    A ` <. x , ( A ` <. y , v >. ) >.
                  )
                  =
                  (
                    ( A ` <. ( B ` <. x , y >. ) , v >. )
                    ( +g ` V )
                    ( A ` <. y , ( A ` <. x , v >. ) >. )
                  )
                )
    )
  ) $.
$}

${
  $d V b $.

  q20971632-finite-dimensional-definition $a |- (
    ( Q20971632FiniteDimensional V )
    <->
    E. b e. ( LBasis ` V )
      b e. Fin
  ) $.
$}

${
  $d B D L n j x y z $.

  q20971632-solvable-definition $a |- (
    ( Q20971632Solvable L B )
    <->
    E. n e. NN0
      E. D e. ( ( ~P ( Base ` L ) ) ^m ( 0 ... n ) )
        (
          ( D ` 0 ) = ( Base ` L )
          /\
          ( D ` n ) = { ( 0g ` L ) }
          /\
          A. j e. ( 0 ..^ n )
            (
              D ` ( j + 1 )
            )
            =
            (
              ( LSpan ` L )
              `
              {
                z e. ( Base ` L ) |
                  E. x e. ( D ` j )
                    E. y e. ( D ` j )
                      z = ( B ` <. x , y >. )
              }
            )
        )
  ) $.
$}

${
  $d A V c n t v x j $.

  q20971632-generalized-eigenvector-definition $a |- (
    ( Q20971632GenEigen V A x c v )
    <->
    E. n e. NN0
      E. t e. ( ( Base ` V ) ^m ( 0 ... n ) )
        (
          ( t ` 0 ) = v
          /\
          ( t ` n ) = ( 0g ` V )
          /\
          A. j e. ( 0 ..^ n )
            (
              t ` ( j + 1 )
            )
            =
            (
              ( A ` <. x , ( t ` j ) >. )
              ( -g ` V )
              (
                c
                ( .s ` V )
                ( t ` j )
              )
            )
        )
  ) $.
$}

${
  $d A K L V W c i v w x $.

  q20971632-triangularizable-definition $a |- (
    ( Q20971632Triangularizable K L V A )
    <->
    A. x e. ( Base ` L )
      A. v e. ( Base ` V )
        E. W e. Fin
          E. c e. ( ( Base ` K ) ^m W )
            E. w e. ( ( Base ` V ) ^m W )
              (
                v = ( V gsum w )
                /\
                A. i e. W
                  (
                    Q20971632GenEigen
                    V
                    A
                    x
                    ( c ` i )
                    ( w ` i )
                  )
              )
  ) $.
$}

${
  $d A B K L V f v x $.

  thousand-theorems-q20971632-lie-theorem $a |-
    A. K A. L A. V A. B A. A
      (
        (
          ( Q20971632LieAlgebra K L B )
          /\
          ( Q20971632LieModule K L V B A )
          /\
          ( chr ` K ) = 0
          /\
          ( Q20971632FiniteDimensional V )
          /\
          E. v e. ( Base ` V )
            v =/= ( 0g ` V )
          /\
          ( Q20971632Solvable L B )
          /\
          ( Q20971632Triangularizable K L V A )
        )
        ->
        E. f e. ( L LMHom ( ringLMod ` K ) )
          E. v e. ( Base ` V )
            (
              v =/= ( 0g ` V )
              /\
              A. x e. ( Base ` L )
                (
                  A ` <. x , v >.
                )
                =
                (
                  ( f ` x )
                  ( .s ` V )
                  v
                )
            )
      )
  $.
$}
