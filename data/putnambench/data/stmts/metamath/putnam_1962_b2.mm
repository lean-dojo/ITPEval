$(
  Statement-only formalization of PutnamBench artifact putnam_1962_b2:
  existence of a function from the reals to subsets of the positive integers
  that is strictly increasing under proper inclusion. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The set.mm classes RR, NN, and ~P NN represent the reals, positive
  integers, and their power set. The native relation C. is proper subsethood.
  The final unproved $a assertion preserves the internal existential
  quantifier over the set-valued function and the universal quantifiers over
  all ordered pairs of real numbers.
$)

${
  $d F a b $.

  putnambench-putnam-1962-b2 $a |- E. F
    (
      F : RR --> ~P NN
      /\
      A. a e. RR A. b e. RR
        (
          a < b
          ->
          ( F ` a ) C. ( F ` b )
        )
    )
  $.
$}
