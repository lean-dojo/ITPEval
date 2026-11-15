$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_b1: nonexistence of four real univariate polynomials whose
  two-product sum is identically 1 + xy + x^2 y^2. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` RRfld ) is set.mm's ring of all finite-support
  univariate real polynomials, and eval1 evaluates such a polynomial at an
  arbitrary real input. Thus a, b, c, and d range over exactly the source
  polynomial objects, while x and y retain their universal real domains.

  The ground-truth solution is False, so the source biconditional is
  equivalent to the negation of the full existential polynomial identity
  below. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof declaration.
$)

${
  $d a b c d x y $.

  putnambench-putnam-2003-b1 $a |- -.
    E. a e. ( Base ` ( Poly1 ` RRfld ) )
      E. b e. ( Base ` ( Poly1 ` RRfld ) )
        E. c e. ( Base ` ( Poly1 ` RRfld ) )
          E. d e. ( Base ` ( Poly1 ` RRfld ) )
            A. x e. RR
              A. y e. RR
                (
                  (
                    1
                    +
                    ( x x. y )
                  )
                  +
                  (
                    ( x ^ 2 )
                    x.
                    ( y ^ 2 )
                  )
                )
                =
                (
                  (
                    ( ( ( eval1 ` RRfld ) ` a ) ` x )
                    x.
                    ( ( ( eval1 ` RRfld ) ` c ) ` y )
                  )
                  +
                  (
                    ( ( ( eval1 ` RRfld ) ` b ) ` x )
                    x.
                    ( ( ( eval1 ` RRfld ) ` d ) ` y )
                  )
                )
  $.
$}
