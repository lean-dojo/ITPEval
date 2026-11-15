$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_a4: the assertion that the stated closure conditions force a
  set of rational numbers to contain every rational number is false. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  The bounded quantifier over ~P QQ ranges over every subset S of the
  rationals. The three nested implications retain the source assumptions:
  membership of zero, closure under adding and subtracting one, and closure
  under x |-> 1 / (x * (x - 1)) away from zero and one. The conclusion
  universally quantifies the rational r.

  The biconditional with F. exactly represents the specified answer False.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d S r x $.

  putnambench-putnam-2009-a4 $a |- (
    (
      A. S e. ~P QQ
        (
          0 e. S
          ->
          (
            A. x e. S
              (
                ( x + 1 ) e. S
                /\
                ( x - 1 ) e. S
              )
            ->
            (
              A. x e. S
                (
                  x e/ { 0 , 1 }
                  ->
                  ( 1 / ( x x. ( x - 1 ) ) ) e. S
                )
              ->
              A. r e. QQ r e. S
            )
          )
        )
    )
    <-> F.
  ) $.
$}
