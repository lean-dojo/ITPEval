$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_a6: the number of admissible ordered pairs of subsets of
  {1, ..., 10}, where every element of either subset exceeds the cardinality
  of the other subset, is 17711. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier ( 1 ... 10 ) is exactly {1, ..., 10}; its power set therefore
  ranges over all source subsets. Each element p of the Cartesian product is
  an ordered pair, with 1st ` p and 2nd ` p its two components. The restricted
  universal quantifiers state the two admissibility inequalities with their
  original scopes, and # gives the finite cardinality of the resulting set.

  The right side is the explicit answer 17711 recorded by both ground-truth
  sources. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof declaration.
$)

${
  $d p s t $.

  putnambench-putnam-1990-a6 $a |-
    (
      #
      `
      {
        p e.
          (
            ~P ( 1 ... ; 1 0 )
            X.
            ~P ( 1 ... ; 1 0 )
          )
        |
        (
          A. s e. ( 1st ` p )
            ( # ` ( 2nd ` p ) ) < s
          /\
          A. t e. ( 2nd ` p )
            ( # ` ( 1st ` p ) ) < t
        )
      }
    )
    =
    ; ; ; ; 1 7 7 1 1
  $.
$}
