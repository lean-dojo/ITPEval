$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_b3: every red-blue coloring of the positive reals becomes
  entirely red after finitely many iterations of the same-color-distance
  recoloring operation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A coloring is represented by a subset X of RR, with membership meaning
  red. P22B3Recolor is a total function on the full power set of RR. Its
  value at X contains exactly those real d for which there are positive
  reals p < q of the same color with q - p = d. The biconditional of
  memberships is exactly equality of the two source truth values.

  IterComp is set.mm's native finite-iteration operator, including the
  identity iterate at k = 0. The final assertion quantifies over every
  coloring and retains the internally existential finite iterate. Since the
  ground-truth solution is True, this assertion is logically equivalent to
  the source proposition being biconditional with its solution proposition.
  Every declaration below is an unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c P22B3Recolor $.

p22b3-recolor-syntax $a class P22B3Recolor $.

${
  $d X d k p q $.

  p22b3-recolor-definition $a |- P22B3Recolor = (
    X e. ( ~P RR ) |->
      {
        d e. RR |
        E. p e. RR E. q e. RR
          (
            0 < p
            /\
            (
              0 < q
              /\
              (
                p < q
                /\
                (
                  ( p e. X <-> q e. X )
                  /\
                  ( q - p ) = d
                )
              )
            )
          )
      }
  ) $.

  putnambench-putnam-2022-b3 $a |- A. X e. ( ~P RR )
    E. k e. NN0 A. p e. RR
      (
        0 < p
        ->
        p
        e.
        (
          (
            ( IterComp ` P22B3Recolor )
            `
            k
          )
          `
          X
        )
      )
  $.
$}
