$(
  Statement-only formalization of Thousand Theorems corpus artifact Q869647
  (thousand-theorems__metamath__Q869647), "Szpilrajn extension theorem":
  every partial order on an arbitrary carrier extends to a linear order on
  the same carrier. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A type is represented by an arbitrary set A, and its binary relations by
  subsets of A X. A. The antecedent states exactly that R is reflexive,
  transitive, and antisymmetric on A. The conclusion keeps the extending
  relation S existentially quantified and states that S has those same three
  laws, is total on A, and contains R.

  The final declaration is the single unproved corpus $a statement. This
  database contains no $p proof statement.
$)

${
  $d A R S x y z $.

  thousand-theorems-q869647-szpilrajn-extension $a |- (
    A. A A. R
      (
        (
          R C_ ( A X. A )
          /\
          (
            A. x e. A x R x
            /\
            (
              A. x e. A A. y e. A A. z e. A
                ( ( x R y /\ y R z ) -> x R z )
              /\
              A. x e. A A. y e. A
                ( ( x R y /\ y R x ) -> x = y )
            )
          )
        )
        ->
        E. S
          (
            S C_ ( A X. A )
            /\
            (
              A. x e. A x S x
              /\
              (
                A. x e. A A. y e. A A. z e. A
                  ( ( x S y /\ y S z ) -> x S z )
                /\
                (
                  A. x e. A A. y e. A
                    ( ( x S y /\ y S x ) -> x = y )
                  /\
                  (
                    A. x e. A A. y e. A ( x S y \/ y S x )
                    /\
                    R C_ S
                  )
                )
              )
            )
          )
      )
  ) $.
$}
