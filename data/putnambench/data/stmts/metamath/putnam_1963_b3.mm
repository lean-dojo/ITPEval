$(
  Statement-only formalization of PutnamBench artifact putnam_1963_b3:
  classification of twice-differentiable real functions satisfying
  f(x)^2 - f(y)^2 = f(x+y)f(x-y) as scaled hyperbolic-sine, linear, or
  sine functions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of total real functions. Membership of every real
  number in the domains of the first two entries of ( RR Dn F ) expresses
  global twice differentiability. The existential alternatives inline the
  solution set documented by the Isabelle and Lean sources and defined by
  the Rocq source. The final declaration is one unproved $a statement.
$)

${
  $d x A $.
  $d x F $.
  $d x k $.

  putnambench-putnam-1963-b3 $a |- A. F e. ( RR ^m RR )
    (
      (
        RR C_ dom ( ( RR Dn F ) ` 1 )
        /\
        RR C_ dom ( ( RR Dn F ) ` 2 )
      )
      ->
      (
        A. x e. RR A. y e. RR
          (
            ( ( F ` x ) ^ 2 ) - ( ( F ` y ) ^ 2 )
          )
          =
          (
            ( F ` ( x + y ) )
            x.
            ( F ` ( x - y ) )
          )
        <->
        E. A e. RR E. k e. RR
          (
            F =
              (
                x e. RR |->
                  ( A x. ( sinh ` ( k x. x ) ) )
              )
            \/
            (
              F = ( x e. RR |-> ( A x. x ) )
              \/
              F =
                (
                  x e. RR |->
                    ( A x. ( sin ` ( k x. x ) ) )
                )
            )
          )
      )
    )
  $.
$}
