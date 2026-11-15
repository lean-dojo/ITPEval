$(
  Statement-only formalization of Thousand Theorems corpus artifact Q853067
  (thousand-theorems__metamath__Q853067), "Solutions to Pell's equation":
  every natural-number solution of x^2 - (a^2 - 1)y^2 = 1 for a > 1 occurs
  in the Pell sequence recursively generated from (1,0). This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The source's proof-valued parameter a1 : 1 < a is represented by the
  antecedent 1 < a. For the internally existential index n, the functions f
  and g on 0 ... n are the finite graphs of Pell.xn and Pell.yn. Their initial
  values, mutual recurrence, and endpoint equalities exactly expand the Lean
  definitions. Existence of these finite graphs is bidirectionally equivalent
  to membership in the source's recursively defined Pell sequence.

  Q853067NatSub is Lean's truncated subtraction on natural numbers, used both
  in d = a*a-1 and in the Pell equation. All quantified values are in NN0.
  The auxiliary $a declarations are syntax and a faithful definition only.
  The final $a assertion is unproved, and this database contains no $p proof
  statement.
$)

$c Q853067NatSub $.

q853067-nat-sub-syntax
  $a class ( Q853067NatSub A B ) $.

q853067-nat-sub-definition $a |- (
  Q853067NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d a f g n k x y $.

  thousand-theorems-q853067-solutions-to-pell-equation $a |-
    A. a e. NN0
      A. x e. NN0
        A. y e. NN0
          (
            (
              1 < a
              /\
              (
                Q853067NatSub
                  ( x x. x )
                  (
                    (
                      ( Q853067NatSub ( a x. a ) 1 )
                      x.
                      y
                    )
                    x.
                    y
                  )
                =
                1
              )
            )
            ->
            E. n e. NN0
              E. f e. ( NN0 ^m ( 0 ... n ) )
                E. g e. ( NN0 ^m ( 0 ... n ) )
                  (
                    (
                      (
                        ( f ` 0 ) = 1
                        /\
                        ( g ` 0 ) = 0
                      )
                      /\
                      A. k e. ( 0 ..^ n )
                        (
                          (
                            f ` ( k + 1 )
                          )
                          =
                          (
                            (
                              ( f ` k )
                              x.
                              a
                            )
                            +
                            (
                              ( Q853067NatSub ( a x. a ) 1 )
                              x.
                              ( g ` k )
                            )
                          )
                          /\
                          (
                            g ` ( k + 1 )
                          )
                          =
                          (
                            ( f ` k )
                            +
                            (
                              ( g ` k )
                              x.
                              a
                            )
                          )
                        )
                    )
                    /\
                    (
                      ( f ` n ) = x
                      /\
                      ( g ` n ) = y
                    )
                  )
          )
  $.
$}
