$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_b2: globally differentiable nonconstant real functions obeying
  the complex multiplication addition laws have unit squared norm everywhere
  when the derivative of the first function at zero is zero. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of total real-valued functions. Containment of RR in
  dom ( RR _D f ) and dom ( RR _D g ) expresses differentiability everywhere.
  Equality with x e. RR |-> c is equality with a constant real function, so
  the negated existential says that neither f nor g is constant. The two
  addition identities and the unit-norm conclusion are stated pointwise over
  all real inputs. The final declaration is one unproved $a statement.
$)

${
  $d c f g x y $.

  putnambench-putnam-1991-b2 $a |-
    A. f e. ( RR ^m RR )
    A. g e. ( RR ^m RR )
      (
        (
          (
            -. E. c e. RR
              (
                f = ( x e. RR |-> c )
                \/
                g = ( x e. RR |-> c )
              )
            /\
            (
              RR C_ dom ( RR _D f )
              /\
              RR C_ dom ( RR _D g )
            )
          )
          /\
          (
            A. x e. RR A. y e. RR
              ( f ` ( x + y ) )
              =
              (
                ( ( f ` x ) x. ( f ` y ) )
                -
                ( ( g ` x ) x. ( g ` y ) )
              )
            /\
            A. x e. RR A. y e. RR
              ( g ` ( x + y ) )
              =
              (
                ( ( f ` x ) x. ( g ` y ) )
                +
                ( ( g ` x ) x. ( f ` y ) )
              )
          )
        )
        ->
        (
          ( ( RR _D f ) ` 0 ) = 0
          ->
          A. x e. RR
            (
              ( ( f ` x ) ^ 2 )
              +
              ( ( g ` x ) ^ 2 )
            )
            =
            1
        )
      )
  $.
$}
