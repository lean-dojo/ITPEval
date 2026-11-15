$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_b2: existence of a real polynomial whose floor at every
  positive integer counts the representations of that integer as a sum of
  powers of two, with each power used at most three times. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  A source multiset is represented by its multiplicity function c on NN0:
  c(k) is the number of copies of 2^k. Requiring c to take values in
  {0,1,2,3} gives exactly the source multiplicity bound, and requiring its
  support to be finite gives exactly the finite multisets. This
  representation is bijective, so the cardinality below is the source f(n),
  without counting different enumerations of one multiset separately.

  Poly1 over RRfld is set.mm's univariate real polynomial ring, eval1 is
  polynomial evaluation, and |_ is the real floor function. The ground-truth
  annotation specifies the solution proposition as True, so its biconditional
  with polynomial existence is equivalent to the assertion below.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d P c j k n $.

  putnambench-putnam-1983-b2 $a |-
    E. P e. ( Base ` ( Poly1 ` RRfld ) )
      A. n e. NN
        (
          |_
          `
          ( ( ( ( eval1 ` RRfld ) ` P ) ` n ) )
        )
        =
        (
          #
          `
          {
            c e. ( ( 0 ... 3 ) ^m NN0 )
            |
            (
              {
                j e. NN0
                |
                ( c ` j ) =/= 0
              }
              e. Fin
              /\
              (
                sum_ k e.
                  {
                    j e. NN0
                    |
                    ( c ` j ) =/= 0
                  }
                  (
                    ( c ` k )
                    x.
                    ( 2 ^ k )
                  )
              )
              =
              n
            )
          }
        )
  $.
$}
