$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_a5: every infinitely continuously differentiable nonnegative
  real function with values zero at 0 and one at 1 has a positive-order
  derivative that is negative at some real point. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is SetMM's class of total real-valued functions. Membership in
  the intersection of the range of ( C^n ` RR ) states continuous
  differentiability through every nonnegative order, and ( RR Dn F ) is
  the sequence of iterated real derivatives. NN is the class of positive
  integers, so both the derivative order and the real point in the
  conclusion remain internally existentially quantified.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d F n x $.

  putnambench-putnam-2018-a5 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          (
            F e. |^| ran ( C^n ` RR )
            /\
            (
              ( F ` 0 ) = 0
              /\
              ( F ` 1 ) = 1
            )
          )
          /\
          A. x e. RR
            0 <_ ( F ` x )
        )
        ->
        E. n e. NN E. x e. RR
          ( ( ( RR Dn F ) ` n ) ` x ) < 0
      )
  $.
$}
