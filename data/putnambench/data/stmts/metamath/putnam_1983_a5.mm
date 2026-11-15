$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_a5: existence of a positive real number alpha such that
  floor(alpha^n) - n is even for every positive integer n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers, |_ is the real floor
  function, and exponentiation by n in NN agrees with the source's natural
  power. Evenness of the integer floor(alpha^n) - n is expressed
  definitionally by an internally existential integer k whose double equals
  that difference.

  The source's specified solution proposition is True, so its biconditional
  is equivalent to the existential assertion below. The final declaration is
  a single unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d a k n $.

  putnambench-putnam-1983-a5 $a |-
    E. a e. RR
      (
        0 < a
        /\
        A. n e. NN
          E. k e. ZZ
            ( ( |_ ` ( a ^ n ) ) - n ) = ( 2 x. k )
      )
  $.
$}
