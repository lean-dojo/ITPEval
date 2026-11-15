$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_b4: existence of an uncountable almost-disjoint family of
  nonempty subsets of a countably infinite set, identified with the source's
  solution proposition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's standard countably infinite set of natural numbers including
  zero. Restricting C to ~P ~P NN0 makes it a family of subsets of this
  carrier. The negated existential injection says exactly that C is
  uncountable; the remaining clauses say that every member is nonempty and
  that the intersection of every two distinct members is finite.

  Using NN0 directly matches the Isabelle source. It is equivalent to Lean's
  existential countably infinite carrier because a bijection with NN0
  transports the family and preserves nonemptiness, distinctness, finite
  intersections, and uncountability in both directions.

  The resolved answer is True, so the final declaration directly asserts
  existence of the family. It is the single unproved $a corpus statement,
  and this database contains no $p proof statement.
$)

${
  $d a b c f r $.

  putnambench-putnam-1989-b4 $a |-
      E. c e. ( ~P ( ~P NN0 ) )
        (
          -. E. f f : c -1-1-> NN0
          /\
          (
            A. r e. c r =/= (/)
            /\
            A. a e. c A. b e. c
              (
                a =/= b
                ->
                ( a i^i b ) e. Fin
              )
          )
        )
  $.
$}
