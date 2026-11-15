$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1052678
  (thousand-theorems__metamath__Q1052678), "Baire category theorem": in an
  arbitrary Baire topological space, the intersection of any countable family
  of open dense subsets is dense. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1052678Baire J X is the defining Baire-space property for a topology J on
  the arbitrary carrier X: every sequence of open dense subsets of X has
  dense intersection. The sequence space ( ( ~P X ) ^m NN0 ) preserves the
  source's arbitrary natural-number-indexed families.

  In the final assertion, S is an arbitrary countable set of subsets of X.
  Membership in J expresses openness, and closure equal to X expresses
  density. The intersection is written X i^i |^| S so that the empty-family
  case is the typed universal subset X, matching Lean's sInter convention.

  The final declaration is the single unproved corpus $a statement. The
  preceding $a declarations are syntax and a faithful definition only. This
  database contains no $p proof statement.
$)

$c Q1052678Baire $.

q1052678-baire-syntax $a wff ( Q1052678Baire J X ) $.

${
  $d F J X n $.

  q1052678-baire-definition $a |- (
    ( Q1052678Baire J X )
    <->
    A. F e. ( ( ~P X ) ^m NN0 )
      (
        A. n e. NN0
          (
            ( F ` n ) e. J
            /\
            ( ( cls ` J ) ` ( F ` n ) ) = X
          )
        ->
        ( ( cls ` J ) ` |^| ran F ) = X
      )
  ) $.
$}

${
  $d J S U X $.

  thousand-theorems-q1052678-baire-category $a |-
    A. X A. J A. S
      (
        (
          (
            J e. ( TopOn ` X )
            /\
            ( Q1052678Baire J X )
          )
          /\
          (
            S e. ( ~P ~P X )
            /\
            (
              S ~<_ _om
              /\
              A. U e. S
                (
                  U e. J
                  /\
                  ( ( cls ` J ) ` U ) = X
                )
            )
          )
        )
        ->
        ( ( cls ` J ) ` ( X i^i |^| S ) ) = X
      )
  $.
$}
