$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_a5: nonexistence of a finite Abelian group whose product of
  all element orders is 2^2009. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Abel ranges over arbitrary Abelian group structures,
  Base ` G is the full carrier, Fin is the class of finite sets, and
  ( od ` G ) ` g is the group-theoretic order of the carrier element g.
  The finite product therefore ranges over every element exactly once.

  The biconditional with F. represents the source's specified answer False.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d G g $.

  putnambench-putnam-2009-a5 $a |- (
    (
      E. G
        (
          (
            G e. Abel
            /\
            ( Base ` G ) e. Fin
          )
          /\
          prod_ g e. ( Base ` G )
            ( ( od ` G ) ` g )
          =
          ( 2 ^ ; ; ; 2 0 0 9 )
        )
    )
    <-> F.
  ) $.
$}
