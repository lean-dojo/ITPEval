$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_a3: the real exponents for which the series with terms
  (((1/n) / sin(1/n)) - 1)^x converges are exactly those greater than
  one half. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, the inclusive interval 1 ... n is empty at zero and otherwise
  gives exactly the source partial sum. The internally existential real L and
  set.mm's sequence-limit relation express convergence without externalizing
  a witness. Each summand uses set.mm's complex power ^c; its base is positive
  for every positive integer n, so ^c agrees with the source real power.

  The Lean and Rocq formulas, the Lean problem text, and all three solution
  specifications place the exponent on each summand. The Isabelle theorem
  instead places powr x outside the finite sum, which conflicts with its own
  adjacent solution specification x > 1/2. The assertion below preserves the
  resulting unambiguous common intended series statement.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d L m n x $.

  putnambench-putnam-1988-a3 $a |- A. x e. RR
    (
      E. L e. RR
        (
          n e. NN0 |->
            sum_ m e. ( 1 ... n )
              (
                (
                  (
                    ( 1 / m )
                    /
                    ( sin ` ( 1 / m ) )
                  )
                  -
                  1
                )
                ^c
                x
              )
        )
        ~~>
        L
      <->
      ( 1 / 2 ) < x
    )
  $.
$}
