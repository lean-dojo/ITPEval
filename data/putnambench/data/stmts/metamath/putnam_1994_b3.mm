$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_b3: characterization of the real exponents for which every
  positive globally differentiable real function with f'(x) > f(x)
  eventually exceeds exp(k x). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function f ranges over all total real-valued functions. Containment of
  RR in dom ( RR _D f ) says that f is differentiable at every real point,
  while the following restricted universal retains positivity and the strict
  derivative inequality pointwise.

  The existential real N remains inside the quantification over f, and the
  conclusion requires the exponential bound at every real x > N. The
  biconditional is the pointwise form of equality between the source set of
  admissible k and the open interval of real numbers below 1.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d N f k x $.

  putnambench-putnam-1994-b3 $a |- A. k e. RR
    (
      A. f e. ( RR ^m RR )
        (
          (
            RR C_ dom ( RR _D f )
            /\
            A. x e. RR
              (
                0 < ( f ` x )
                /\
                ( f ` x ) < ( ( RR _D f ) ` x )
              )
          )
          ->
          E. N e. RR
            A. x e. RR
              (
                N < x
                ->
                ( exp ` ( k x. x ) ) < ( f ` x )
              )
        )
      <->
      k < 1
    )
  $.
$}
