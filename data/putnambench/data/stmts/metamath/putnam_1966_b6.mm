$(
  Statement-only formalization of PutnamBench artifact putnam_1966_b6:
  eventual boundedness of every globally twice-differentiable real solution
  of y''(x) + exp(x)y(x) = 0. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of total real functions. Requiring RR to be contained
  in the domains of the first two entries of ( RR Dn y ) expresses global
  differentiability of y and of its first derivative. The differential
  equation is stated pointwise, and the eventual lower and upper bounds remain
  internally existential. The final declaration is one unproved $a statement.
$)

${
  $d N r s x y $.

  putnambench-putnam-1966-b6 $a |- A. y e. ( RR ^m RR )
    (
      (
        (
          RR C_ dom ( ( RR Dn y ) ` 1 )
          /\
          RR C_ dom ( ( RR Dn y ) ` 2 )
        )
        /\
        A. x e. RR
          (
            ( ( ( RR Dn y ) ` 2 ) ` x )
            +
            ( ( exp ` x ) x. ( y ` x ) )
          )
          =
          0
      )
      ->
      E. r e. RR E. s e. RR E. N e. RR
        A. x e. RR
          (
            N < x
            ->
            ( r <_ ( y ` x ) /\ ( y ` x ) <_ s )
          )
    )
  $.
$}
