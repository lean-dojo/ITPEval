$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_a2: the differentiable real functions whose derivative equals
  every positive-integer forward difference quotient are exactly the affine
  real functions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is set.mm's class of total real-valued functions on the reals.
  Requiring RR to be contained in dom ( RR _D F ) says that F is
  differentiable at every real point, without strengthening differentiability
  to continuous differentiability. NN is the class of positive integers, so
  the nested restricted quantifiers preserve the source's quantification over
  every real x and positive integer n.

  The right side keeps the affine coefficients internally existentially
  quantified over RR. Pointwise equality on RR is equivalent to equality of
  the corresponding total real functions. The final biconditional therefore
  directly classifies exactly the source functions. The declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d F c d n x $.

  putnambench-putnam-2010-a2 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          RR C_ dom ( RR _D F )
          /\
          A. x e. RR A. n e. NN
            ( ( RR _D F ) ` x )
            =
            (
              (
                ( F ` ( x + n ) )
                -
                ( F ` x )
              )
              /
              n
            )
        )
        <->
        E. c e. RR E. d e. RR A. x e. RR
          ( F ` x )
          =
          (
            ( c x. x )
            +
            d
          )
      )
  $.
$}
