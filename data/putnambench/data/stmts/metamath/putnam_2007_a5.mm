$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_a5: divisibility of one more than the number of elements of
  prime order in a finite group. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Grp supplies an arbitrary group, Base ` G is its carrier,
  ( od ` G ) is its group-element order function, Fin is the class of finite
  sets, # is finite cardinality, Prime is the class of natural primes, and ||
  is integer divisibility.

  The restricted class contains exactly the carrier elements whose order is
  p, so its cardinality is the source number n. The conclusion preserves the
  source disjunction n = 0 or p divides n + 1. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d G g n p $.

  putnambench-putnam-2007-a5 $a |-
    A. G A. p e. Prime A. n e. NN0
      (
        (
          (
            G e. Grp
            /\
            ( Base ` G ) e. Fin
          )
          /\
          n
          =
          (
            #
            `
            { g e. ( Base ` G ) |
              ( ( od ` G ) ` g ) = p
            }
          )
        )
        ->
        (
          n = 0
          \/
          p || ( n + 1 )
        )
      )
  $.
$}
