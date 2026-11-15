$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1976_a3: classification of natural prime powers with exponents
  greater than one whose integer absolute difference is one. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers, and Prime is its class of
  natural primes. For natural bases and exponents, SetMM's power operation
  gives the source natural powers; applying abs after subtraction gives the
  same value as the source absolute value after coercion to the integers.

  The biconditional states pointwise equality of the source solution set with
  exactly the two quadruples (3,2,2,3) and (2,3,3,2), in the source order
  (p,r,q,s). The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d p q r s $.

  putnambench-putnam-1976-a3 $a |-
    A. p e. NN0 A. r e. NN0 A. q e. NN0 A. s e. NN0
      (
        (
          (
            (
              p e. Prime
              /\
              q e. Prime
            )
            /\
            (
              1 < r
              /\
              1 < s
            )
          )
          /\
          ( abs ` ( ( p ^ r ) - ( q ^ s ) ) ) = 1
        )
        <->
        (
          (
            (
              (
                p = 3
                /\
                r = 2
              )
              /\
              q = 2
            )
            /\
            s = 3
          )
          \/
          (
            (
              (
                p = 2
                /\
                r = 3
              )
              /\
              q = 3
            )
            /\
            s = 2
          )
        )
      )
  $.
$}
