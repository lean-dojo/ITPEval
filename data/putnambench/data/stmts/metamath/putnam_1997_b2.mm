$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_b2: boundedness in absolute value of every globally
  twice-differentiable real solution of f(x) + f''(x) =
  -x g(x) f'(x) when g is nonnegative. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  f and g range over arbitrary total real-valued functions. Requiring RR to
  be contained in the domains of the first two entries of ( RR Dn f )
  expresses global differentiability of f and of its first derivative. The
  differential equation and nonnegativity of g are stated pointwise on all
  reals.

  The conclusion keeps the bound M internally existential. Bounding
  abs(f(x)) above by m for every real x is equivalent to boundedness of its
  range; the automatic lower bound zero supplies the lower half of the Rocq
  formulation. The final declaration is one unproved $a statement.
$)

${
  $d f g m x $.

  putnambench-putnam-1997-b2 $a |-
    A. f e. ( RR ^m RR )
    A. g e. ( RR ^m RR )
      (
        (
          (
            RR C_ dom ( ( RR Dn f ) ` 1 )
            /\
            RR C_ dom ( ( RR Dn f ) ` 2 )
          )
          /\
          A. x e. RR 0 <_ ( g ` x )
        )
        /\
        A. x e. RR
          (
            ( f ` x )
            +
            ( ( ( RR Dn f ) ` 2 ) ` x )
          )
          =
          (
            (
              ( -u x )
              x.
              ( g ` x )
            )
            x.
            ( ( ( RR Dn f ) ` 1 ) ` x )
          )
        ->
        E. m e. RR
          A. x e. RR
            ( abs ` ( f ` x ) ) <_ m
      )
  $.
$}
