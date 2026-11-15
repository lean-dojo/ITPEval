$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1068085
  (thousand-theorems__metamath__Q1068085), "Closed graph theorem": a linear
  map between complete normed vector spaces over an arbitrary nontrivially
  normed field is continuous when its graph is closed. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  K is a bundled SetMM normed field, and the existential element whose norm
  exceeds one renders Lean's nontrivial-norm assumption. V and W are arbitrary
  normed vector spaces over K whose norm-induced metric spaces are complete.
  The class g is a SetMM linear map V LMHom W and, as a set-theoretic function,
  is itself its graph, a subset of ( Base ` V ) X. ( Base ` W ). Thus
  membership of g in the closed subsets of the product topology is exactly the
  source hypothesis that the graph is closed. The conclusion uses SetMM's
  native class of continuous functions between the two norm topologies.

  The final declaration is the single unproved corpus $a statement; this
  database contains no $p proof statement.
$)

${
  $d K V W c g v w $.

  thousand-theorems-q1068085-closed-graph $a |-
    A. K e. ( NrmRing i^i Field )
      A. V e. { v e. NrmVec | ( Scalar ` v ) = K }
        A. W e. { w e. NrmVec | ( Scalar ` w ) = K }
          A. g e. ( V LMHom W )
            (
              (
                E. c e. ( Base ` K )
                  1 < ( ( norm ` K ) ` c )
                /\
                V e. CMetSp
                /\
                W e. CMetSp
                /\
                g e. (
                  Clsd
                  `
                  ( ( TopOpen ` V ) tX ( TopOpen ` W ) )
                )
              )
              ->
              g e. ( ( TopOpen ` V ) Cn ( TopOpen ` W ) )
            )
  $.
$}
