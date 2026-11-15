$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_b5: classification of continuously differentiable real
  functions that preserve the reduced denominator of every rational input.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of all total real-valued functions, and membership in
  ( ( C^n ` RR ) ` 1 ) is global continuous differentiability through order
  one. The canonical function denom maps each rational to the positive
  denominator of its unique reduced fraction representation. Thus the left
  side states exactly that every rational q is mapped to a rational with the
  same reduced denominator.

  The right side inlines the source solution set: for one internally
  existential integer n, the function is either x |-> x + n everywhere or
  x |-> -x + n everywhere. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d f n q x $.

  putnambench-putnam-2008-b5 $a |-
    A. f e. ( RR ^m RR )
      (
        (
          f e. ( ( C^n ` RR ) ` 1 )
          /\
          A. q e. QQ
            (
              ( f ` q ) e. QQ
              /\
              ( denom ` ( f ` q ) ) = ( denom ` q )
            )
        )
        <->
        E. n e. ZZ
          (
            (
              A. x e. RR
                ( f ` x ) = ( x + n )
            )
            \/
            (
              A. x e. RR
                ( f ` x ) = ( ( -u x ) + n )
            )
          )
      )
  $.
$}
