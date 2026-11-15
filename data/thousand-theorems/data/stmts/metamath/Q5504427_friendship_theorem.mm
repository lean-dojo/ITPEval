$(
  Statement-only formalization of Thousand Theorems corpus artifact Q5504427
  (thousand-theorems__metamath__Q5504427), "Friendship theorem": every
  nonempty finite simple graph in which each pair of distinct vertices has
  exactly one common neighbor contains a vertex adjacent to every other
  vertex. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite Lean vertex type is represented by an arbitrary nonempty finite
  set s. The edge set r is required to be an irreflexive symmetric relation
  on s. The restricted unique existential is exactly the assertion that the
  two distinct vertices have one common r-neighbor.

  The declaration below is the single unproved corpus $a statement. This file
  introduces no $p proof statement.
$)

${
  $d p r s u v w $.

  thousand-theorems-q5504427-friendship $a |- (
    A. s A. r
      (
        (
          (
            (
              s e. Fin
              /\
              s =/= (/)
            )
            /\
            (
              r C_ ( s X. s )
              /\
              (
                A. v e. s -. <. v , v >. e. r
                /\
                A. v e. s A. w e. s
                  ( <. v , w >. e. r <-> <. w , v >. e. r )
              )
            )
          )
          /\
          A. v e. s A. w e. s
            (
              v =/= w
              ->
              E! u e. s
                (
                  <. v , u >. e. r
                  /\
                  <. w , u >. e. r
                )
            )
        )
        ->
        E. p e. s A. w e. s
          ( p =/= w -> <. p , w >. e. r )
      )
  ) $.
$}
