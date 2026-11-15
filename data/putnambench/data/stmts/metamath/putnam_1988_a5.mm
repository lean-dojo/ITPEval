$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_a5: existence and uniqueness on the positive reals of a
  positive-valued real function satisfying f(f(x)) = 6x - f(x).
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F and G range over all total real-valued functions. The functional
  equation, positivity condition, and equality used for uniqueness are all
  restricted to the full open positive-real interval ( 0 (,) +oo ), so
  values at nonpositive inputs remain unconstrained as in the Lean and
  Isabelle sources.

  The Rocq source instead fixes every nonpositive value to zero. Restriction
  to the positive reals and extension by zero are inverse on its admissible
  functions, so its whole-function uniqueness is equivalent to the
  positive-domain uniqueness asserted here. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d F G x $.

  putnambench-putnam-1988-a5 $a |-
    E. F e. ( RR ^m RR )
      (
        A. x e. ( 0 (,) +oo )
          (
            ( F ` ( F ` x ) )
            =
            ( ( 6 x. x ) - ( F ` x ) )
            /\
            0 < ( F ` x )
          )
        /\
        A. G e. ( RR ^m RR )
          (
            A. x e. ( 0 (,) +oo )
              (
                ( G ` ( G ` x ) )
                =
                ( ( 6 x. x ) - ( G ` x ) )
                /\
                0 < ( G ` x )
              )
            ->
            A. x e. ( 0 (,) +oo )
              ( F ` x ) = ( G ` x )
          )
      )
  $.
$}
