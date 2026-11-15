$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_b1: every product of two integers at least 2 is expressible
  as xy + xz + yz + 1 for positive integers x, y, and z. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN are the integers and positive integers, respectively.
  Thus binding x, y, and z over NN is definitionally equivalent to binding
  them over ZZ and requiring each to be greater than 0.

  The Lean and Isabelle sources quantify the factors a and b explicitly.
  The Rocq source instead quantifies n > 3 with n nonprime. These
  formulations are equivalent: a product of integers a,b >= 2 is a
  nonprime integer greater than 3, and every nonprime integer greater than
  3 has such a factorization. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d a b x y z $.

  putnambench-putnam-1988-b1 $a |-
    A. a e. ZZ A. b e. ZZ
      (
        ( 2 <_ a /\ 2 <_ b )
        ->
        E. x e. NN E. y e. NN E. z e. NN
          (
            ( a x. b )
            =
            (
              (
                ( ( x x. y ) + ( x x. z ) )
                +
                ( y x. z )
              )
              +
              1
            )
          )
      )
  $.
$}
