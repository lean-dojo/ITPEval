$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_a1: characterization of the integer-valued function on the
  integers satisfying two iterated functional identities and the value
  f(0) = 1 as the function n |-> 1 - n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  ZZ ^m ZZ is set.mm's class of all total integer-valued functions on the
  integers. The outer restricted universal quantifier is the universal
  closure of the source theorem's arbitrary function parameter, and the
  map n e. ZZ |-> 1 - n is its extensional function value.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f n $.

  putnambench-putnam-1992-a1 $a |- A. f e. ( ZZ ^m ZZ )
    (
      f = ( n e. ZZ |-> ( 1 - n ) )
      <->
      (
        A. n e. ZZ
          ( f ` ( f ` n ) ) = n
        /\
        (
          A. n e. ZZ
            ( f ` ( ( f ` ( n + 2 ) ) + 2 ) ) = n
          /\
          ( f ` 0 ) = 1
        )
      )
    )
  $.
$}
