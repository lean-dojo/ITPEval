$(
  Statement-only formalization of "Minkowski's Fundamental Theorem" from
  Hundred Theorems artifact 040. It states that a measurable convex subset of
  finite-dimensional real space, symmetric about the origin and of volume
  greater than 2 to the dimension, contains a nonzero integer-lattice point.
  This file contains no proof.
$)

$[ library/set.mm $]

$(
  For N e. NN, the coordinate set I = ( 1 ... N ) gives the Euclidean space
  RR ^m I. The domain of voln ` I is the collection of Lebesgue-measurable
  subsets of that space. Convexity and symmetry are expanded coordinatewise,
  and ZZ ^m I is the integer lattice.

  The final $a assertion is the unproved corpus statement.
$)

${
  $d N B I t u x y k $.

  ht040-minkowski $a
    |- A. N e. NN A. I
      ( I = ( 1 ... N ) ->
        A. B
          (
            (
              (
                B e. dom ( voln ` I )
                /\
                A. x e. B
                  ( k e. I |-> -u ( x ` k ) ) e. B
              )
              /\
              (
                A. x e. B A. y e. B A. t e. ( 0 [,] 1 )
                  ( k e. I |->
                    (
                      ( ( 1 - t ) x. ( x ` k ) )
                      +
                      ( t x. ( y ` k ) )
                    )
                  ) e. B
                /\
                ( 2 ^ N ) < ( ( voln ` I ) ` B )
              )
            )
            ->
            E. u e. ( ZZ ^m I )
              (
                u e. B
                /\
                u =/= ( k e. I |-> 0 )
              )
          )
      )
  $.
$}
