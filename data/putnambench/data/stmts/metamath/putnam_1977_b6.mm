$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_b6: finite products x_1 a ... x_n a from a finite subgroup
  have cardinality at most three times the square of the subgroup order
  when every (x a)^3 is the group identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Grp is an arbitrary group, H e. ( SubGrp ` G ) is a
  subgroup, Fin and # express finiteness and finite cardinality, and .g is
  integer group exponentiation. Word H is the class of all finite sequences
  over H; deleting the empty word imposes the source condition n >= 1.

  For each remaining word w, composition with the map x |-> x (+g) a
  produces the ordered sequence x_1 a, ..., x_n a. Since every word has a
  consecutive integer domain, G gsum is its left-to-right group product.
  Thus the displayed range is definitionally the source set P, without
  externalizing the finite-sequence witness. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d G H P a h w x y $.

  putnambench-putnam-1977-b6 $a |-
    A. h e. NN0 A. a e. ( Base ` G )
      (
        (
          (
            (
              G e. Grp
              /\
              H e. ( SubGrp ` G )
            )
            /\
            (
              H e. Fin
              /\
              ( # ` H ) = h
            )
          )
          /\
          (
            A. y e. H
              (
                3 ( .g ` G ) ( y ( +g ` G ) a )
              )
              =
              ( 0g ` G )
            /\
            P =
              ran
                (
                  w e. ( Word H \ { (/) } ) |->
                    (
                      G gsum
                        (
                          ( x e. H |-> ( x ( +g ` G ) a ) )
                          o.
                          w
                        )
                    )
                )
          )
        )
        ->
        (
          P e. Fin
          /\
          ( # ` P ) <_ ( 3 x. ( h ^ 2 ) )
        )
      )
  $.
$}
