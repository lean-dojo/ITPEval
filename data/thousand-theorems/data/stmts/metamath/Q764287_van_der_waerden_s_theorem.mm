$(
  Statement-only formalization of Thousand Theorems corpus artifact Q764287
  (thousand-theorems__metamath__Q764287), "Van der Waerden's theorem": every
  finite subset of an arbitrary additively written commutative monoid has a
  monochromatic positive-natural homothetic copy under every finite coloring.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. CMnd supplies an arbitrary commutative monoid, Base ` G is
  its carrier, +g ` G is its operation, and G gsum is its finite generalized
  sum. Renaming that operation additively gives exactly the source
  AddCommMonoid. The finite set S is an arbitrary finite subset of the full
  carrier, K is an arbitrary finite color set, and C is any total coloring.

  For positive a, G gsum ( k e. ( 1 ... a ) |-> s ) is the a-fold sum of s,
  hence the source natural scalar multiple of s by a. The witnesses a, b, and c
  remain internally existential, and the restricted universal quantifier over
  S is exactly the source Finset membership condition.

  The declaration below is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d G S K C a b c s k $.

  thousand-theorems-q764287-van-der-waerden $a |-
    A. G e. CMnd
      A. S e. ( ~P ( Base ` G ) i^i Fin )
        A. K e. Fin
          A. C
            (
              C : ( Base ` G ) --> K
              ->
              E. a e. NN
                E. b e. ( Base ` G )
                  E. c e. K
                    A. s e. S
                      (
                        C `
                        (
                          ( G gsum ( k e. ( 1 ... a ) |-> s ) )
                          ( +g ` G )
                          b
                        )
                      )
                      =
                      c
            )
  $.
$}
