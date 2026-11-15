$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1050203
  (thousand-theorems__metamath__Q1050203), "Cantor's intersection theorem":
  a nonempty downward-directed family of nonempty compact closed subsets of
  an arbitrary topological space has nonempty intersection. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  J ranges over topologies on the arbitrary carrier X, and S ranges over
  families of subsets of X. The common-lower-bound clause is exactly
  directedness under reverse inclusion. For each U in S, ( J |`t U ) e. Comp
  states compactness of the subspace topology, while U e. ( Clsd ` J ) states
  closedness in X.

  The final declaration is the single unproved $a corpus statement. This
  database contains no $p proof statement.
$)

${
  $d J S U V W X $.

  thousand-theorems-q1050203-cantor-intersection $a |-
    A. X A. J A. S
      (
        (
          J e. ( TopOn ` X )
          /\
          (
            S e. ( ~P ~P X )
            /\
            S =/= (/)
          )
        )
        ->
        (
          (
            A. U e. S A. V e. S
              E. W e. S
                (
                  W C_ U
                  /\
                  W C_ V
                )
            /\
            A. U e. S
              (
                U =/= (/)
                /\
                (
                  ( J |`t U ) e. Comp
                  /\
                  U e. ( Clsd ` J )
                )
              )
          )
          ->
          |^| S =/= (/)
        )
      )
  $.
$}
