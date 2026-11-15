$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2002_b5: existence of a natural number that is a three-digit
  palindrome in at least 2002 integer bases. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For b >= 2, a least-significant-digit-first base-b expansion has length
  three and is palindromic exactly when its digits are a,d,a, where
  1 <= a < b and 0 <= d < b. The displayed positional-value equation
  expresses precisely that condition. For b = 1, the sources define the
  digit list as n copies of 1, so it has length three and is palindromic
  exactly when n = 3.

  Thus the restricted class is exactly the source set of qualifying natural
  bases, including its unary-base convention. For each fixed n this class is
  finite, so set.mm's cardinality operator agrees with the source finite
  cardinality. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d a b d n $.

  putnambench-putnam-2002-b5 $a |-
    E. n e. NN0
      (
        ; ; ; 2 0 0 2
        <_
        (
          #
          `
          {
            b e. NN
            |
            (
              (
                b = 1
                /\
                n = 3
              )
              \/
              (
                1 < b
                /\
                E. a e. NN E. d e. NN0
                  (
                    (
                      a < b
                      /\
                      d < b
                    )
                    /\
                    n
                    =
                    (
                      (
                        a x. ( b ^ 2 )
                      )
                      +
                      (
                        d x. b
                      )
                    )
                    +
                    a
                  )
              )
            )
          }
        )
      )
  $.
$}
