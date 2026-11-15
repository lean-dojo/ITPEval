$(
  Statement-only formalization of Thousand Theorems corpus artifact Q258374
  (thousand-theorems__metamath__Q258374), "Carath&eacute;odory's theorem (measure
  theory)": the sets satisfying Carath&eacute;odory's splitting criterion for an
  arbitrary outer measure form a sigma-algebra. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q258374OuterMeasure X O says that O is an extended-nonnegative-valued outer
  measure on every subset of the arbitrary base set X: it vanishes on the
  empty set, is monotone, and is countably subadditive for every NN0-indexed
  sequence of subsets.

  Q258374Caratheodory X O is the family of subsets E of X such that every
  test set A is split additively by E:

    O(A) = O(A intersect E) + O(A difference E).

  The final unproved $a statement says that this exact family is a
  sigma-algebra on X and restates its membership criterion. All preceding
  root-artifact $a declarations are syntax or faithful definitions, and the
  root artifact declares no $p proof statement.
$)

$c Q258374OuterMeasure Q258374Caratheodory $.

q258374-outer-measure-syntax
  $a wff ( Q258374OuterMeasure X O ) $.
q258374-caratheodory-syntax
  $a class ( Q258374Caratheodory X O ) $.

${
  $d A B F O X n $.

  q258374-outer-measure-definition $a |- (
    ( Q258374OuterMeasure X O )
    <->
    (
      O : ~P X --> ( 0 [,] +oo )
      /\
      (
        (
          ( O ` (/) ) = 0
          /\
          A. A e. ~P X
            A. B e. ~P X
              (
                A C_ B
                ->
                ( O ` A ) <_ ( O ` B )
              )
        )
        /\
        A. F e. ( ( ~P X ) ^m NN0 )
          ( O ` U. ran F )
          <_
          sum* n e. NN0 ( O ` ( F ` n ) )
      )
    )
  ) $.
$}

${
  $d A E O X $.

  q258374-caratheodory-definition $a |- (
    Q258374Caratheodory X O
    =
    { E e. ~P X |
      A. A e. ~P X
        ( O ` A )
        =
        (
          ( O ` ( A i^i E ) )
          +e
          ( O ` ( A \ E ) )
        )
    }
  ) $.
$}

${
  $d A E O X $.

  thousand-theorems-q258374-caratheodory-measure-theory $a |-
    A. X A. O
      (
        (
          X e. _V
          /\
          ( Q258374OuterMeasure X O )
        )
        ->
        (
          ( Q258374Caratheodory X O )
            e. ( sigAlgebra ` X )
          /\
          A. E e. ~P X
            (
              E e. ( Q258374Caratheodory X O )
              <->
              A. A e. ~P X
                ( O ` A )
                =
                (
                  ( O ` ( A i^i E ) )
                  +e
                  ( O ` ( A \ E ) )
                )
            )
        )
      )
  $.
$}
