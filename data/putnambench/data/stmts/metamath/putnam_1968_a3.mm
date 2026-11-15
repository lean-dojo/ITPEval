$(
  Statement-only formalization of PutnamBench artifact putnam_1968_a3:
  every finite set has an ordering of all its subsets that starts with the
  empty set and changes exactly one element at each step. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  An arbitrary finite set A represents the source finite carrier. The
  bijection F from the half-open interval 0 ..^ (# ` ~P A) onto ~P A is
  exactly a list in which every subset of A occurs once. Using the cardinality
  of the powerset directly is equivalent to the source existential length.

  For consecutive indices, cardinality one of the symmetric difference is
  equivalent to obtaining the next subset by adding or removing one element.
  The final declaration is the single unproved $a corpus statement.
$)

${
  $d A F i $.

  putnambench-putnam-1968-a3 $a |- A. A e. Fin
    E. F
      (
        (
          F : ( 0 ..^ ( # ` ~P A ) ) -1-1-onto-> ~P A
          /\
          ( F ` 0 ) = (/)
        )
        /\
        A. i e. ( 0 ..^ ( ( # ` ~P A ) - 1 ) )
          (
            # `
              (
                ( ( F ` i ) \ ( F ` ( i + 1 ) ) )
                u.
                ( ( F ` ( i + 1 ) ) \ ( F ` i ) )
              )
          )
          =
          1
      )
  $.
$}
