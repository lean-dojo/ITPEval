$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1551745
  (thousand-theorems__metamath__Q1551745), "Binomial inverse theorem": over
  every ring and arbitrary finite matrix index carriers, chosen two-sided
  inverses satisfy the binomial inverse matrix identity. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Q1551745Mul is multiplication of compatible rectangular matrices over R.
  Q1551745Add and Q1551745Neg are addition and additive inverse in a square
  matrix ring. Q1551745Inv R I A X says that X is the chosen two-sided inverse
  of the square matrix A.

  The final assertion quantifies over the three inverse witnesses carried by
  Lean's Invertible instances: X for A, Y for
  C + C V X U C, and Z for A + U C V. Its implication assumes exactly the
  two inverse equations supplied by each instance and concludes the source
  identity for Z. All auxiliary $a declarations are syntax or faithful
  definitions; the final $a is the single unproved corpus statement, and this
  file contains no $p declaration.
$)

$c Q1551745Mul Q1551745Add Q1551745Neg Q1551745Inv $.

q1551745-mul-syntax $a class
  ( Q1551745Mul R I J K A B ) $.
q1551745-add-syntax $a class
  ( Q1551745Add R I A B ) $.
q1551745-neg-syntax $a class
  ( Q1551745Neg R I A ) $.
q1551745-inv-syntax $a wff
  ( Q1551745Inv R I A B ) $.

${
  $d A B I J K R $.

  q1551745-mul-definition $a |-
    ( Q1551745Mul R I J K A B )
    =
    ( A ( R maMul <. I , J , K >. ) B )
  $.
$}

${
  $d A B I R $.

  q1551745-add-definition $a |-
    ( Q1551745Add R I A B )
    =
    ( A ( +g ` ( I Mat R ) ) B )
  $.
$}

${
  $d A I R $.

  q1551745-neg-definition $a |-
    ( Q1551745Neg R I A )
    =
    ( ( invg ` ( I Mat R ) ) ` A )
  $.
$}

${
  $d A B I R $.

  q1551745-inv-definition $a |- (
    ( Q1551745Inv R I A B )
    <->
    (
      ( Q1551745Mul R I I I B A )
      =
      ( 1r ` ( I Mat R ) )
      /\
      ( Q1551745Mul R I I I A B )
      =
      ( 1r ` ( I Mat R ) )
    )
  ) $.
$}

${
  $d A C M N R U V X Y Z $.

  thousand-theorems-q1551745-binomial-inverse-theorem $a |-
    A. R e. Ring
      A. N e. Fin
        A. M e. Fin
          A. A e. ( ( Base ` R ) ^m ( N X. N ) )
            A. U e. ( ( Base ` R ) ^m ( N X. M ) )
              A. C e. ( ( Base ` R ) ^m ( M X. M ) )
                A. V e. ( ( Base ` R ) ^m ( M X. N ) )
                  A. X e. ( ( Base ` R ) ^m ( N X. N ) )
                    A. Y e. ( ( Base ` R ) ^m ( M X. M ) )
                      A. Z e. ( ( Base ` R ) ^m ( N X. N ) )
                        (
                          (
                            ( Q1551745Inv R N A X )
                            /\
                            (
                              Q1551745Inv R M
                              (
                                Q1551745Add R M C
                                (
                                  Q1551745Mul R M M M
                                  (
                                    Q1551745Mul R M N M
                                    (
                                      Q1551745Mul R M N N
                                      ( Q1551745Mul R M M N C V )
                                      X
                                    )
                                    U
                                  )
                                  C
                                )
                              )
                              Y
                            )
                            /\
                            (
                              Q1551745Inv R N
                              (
                                Q1551745Add R N A
                                (
                                  Q1551745Mul R N M N
                                  ( Q1551745Mul R N M M U C )
                                  V
                                )
                              )
                              Z
                            )
                          )
                          ->
                          Z
                          =
                          (
                            Q1551745Add R N X
                            (
                              Q1551745Neg R N
                              (
                                Q1551745Mul R N N N
                                (
                                  Q1551745Mul R N M N
                                  (
                                    Q1551745Mul R N M M
                                    (
                                      Q1551745Mul R N M M
                                      (
                                        Q1551745Mul R N M M
                                        ( Q1551745Mul R N N M X U )
                                        C
                                      )
                                      Y
                                    )
                                    C
                                  )
                                  V
                                )
                                X
                              )
                            )
                          )
                        )
  $.
$}
