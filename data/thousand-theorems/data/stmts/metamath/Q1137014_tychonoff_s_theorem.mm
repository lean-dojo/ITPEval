$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1137014
  (thousand-theorems__metamath__Q1137014), "Tychonoff's theorem": the
  arbitrarily indexed product of compact subsets of arbitrary topological
  spaces is compact. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  j is an arbitrary family of topologies indexed by a, and s is a family
  assigning to each index a subset of the corresponding carrier. The
  hypothesis that ( ( J ` i ) |`t ( S ` i ) ) belongs to Comp says exactly
  that s(i), with its subspace topology, is compact.

  SetMM's indexed product X_ i e. a ( s ` i ) is the dependent function
  space of points whose i-th coordinate lies in s(i). Restricting the indexed
  product topology ( Xt_ ` j ) to this set gives the same topology as the
  product of the factor subspace topologies, so the conclusion is equivalent
  to compactness of the set of dependent functions in the Lean source.

  The final declaration is the single unproved $a corpus statement. This
  database contains no $p proof statement.
$)

${
  $d a i j s $.

  thousand-theorems-q1137014-tychonoff $a |-
    A. a A. j A. s
      (
        (
          (
            j : a --> Top
            /\
            s Fn a
          )
          /\
          A. i e. a
            ( s ` i ) C_ U. ( j ` i )
        )
        ->
        (
          A. i e. a
            ( ( j ` i ) |`t ( s ` i ) ) e. Comp
          ->
          (
            ( Xt_ ` j )
            |`t
            X_ i e. a ( s ` i )
          ) e. Comp
        )
      )
  $.
$}
