$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_a3: the real functions on the unit interval that preserve
  existence of Cesaro limits are exactly the affine functions there.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function f is an arbitrary total real-valued function on the reals,
  matching the source convention that only its restriction to [0,1] is
  constrained. For each [0,1]-valued real sequence X, the two internally
  existential real limits express existence of the Cesaro limits of X and
  of its pointwise image under f. The finite range 0 ..^ n is exactly the
  source sum over indices below n; its value at n = 0 is irrelevant to
  convergence.

  The right side is the explicit solution set supplied by the ground-truth
  sources: f agrees with x |-> A*x+B throughout [0,1], with unrestricted
  values outside that interval. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A B C D X f i n x $.

  putnambench-putnam-1972-a3 $a |-
    A. f e. ( RR ^m RR )
      (
        (
          A. X e. ( RR ^m NN0 )
            (
              A. i e. NN0 ( X ` i ) e. ( 0 [,] 1 )
              ->
              (
                E. C e. RR
                  (
                    n e. NN0 |->
                      (
                        (
                          sum_ i e. ( 0 ..^ n )
                            ( X ` i )
                        )
                        /
                        n
                      )
                  )
                  ~~>
                  C
                ->
                E. D e. RR
                  (
                    n e. NN0 |->
                      (
                        (
                          sum_ i e. ( 0 ..^ n )
                            ( f ` ( X ` i ) )
                        )
                        /
                        n
                      )
                  )
                  ~~>
                  D
              )
            )
        )
        <->
        E. A e. RR E. B e. RR
          A. x e. ( 0 [,] 1 )
            ( f ` x ) = ( ( A x. x ) + B )
      )
  $.
$}
