$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1968_b2: in every finite group, any subset containing more than
  half of the group has every group element as a product of two elements of
  that subset. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Grp supplies the arbitrary group structure, Base ` G is its
  carrier, +g ` G is its binary group operation, Fin is the class of finite sets,
  and # gives finite cardinality. Since these cardinalities are natural
  numbers, comparison with half the carrier cardinality agrees with the
  floor-division presentation in the Isabelle and Rocq sources.

  The factors x and y remain existentially quantified within the conclusion
  for each arbitrary carrier element g. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A G g x y $.

  putnambench-putnam-1968-b2 $a |- A. G A. A
    (
      (
        (
          (
            G e. Grp
            /\
            ( Base ` G ) e. Fin
          )
          /\
          A C_ ( Base ` G )
        )
        /\
        ( ( # ` ( Base ` G ) ) / 2 ) < ( # ` A )
      )
      ->
      A. g e. ( Base ` G )
        E. x e. A E. y e. A
          g = ( x ( +g ` G ) y )
    )
  $.
$}
