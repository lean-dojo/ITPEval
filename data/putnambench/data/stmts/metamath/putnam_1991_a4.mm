$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_a4: existence of a sequence of closed discs in the real plane
  whose centers have no finite-plane limit point, whose total area is finite,
  and such that every affine line meets at least one disc. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  X and Y are the coordinate sequences of the disc centers, and R is the
  nonnegative radius sequence. Splitting a map from NN0 into RR X. RR into
  its two coordinate maps is a bijective, definitionally equivalent encoding
  of the source sequence of plane centers. Isabelle states nonnegativity
  explicitly. Its omission from the Lean existential is equivalent: replacing
  each radius by its absolute value preserves every squared radius and cannot
  destroy a line intersection.

  The first condition negates the source's exact subsequence characterization
  of a finite-plane limit point: for a proposed point and every positive
  epsilon, a strictly increasing index map would put its entire subsequence
  in the open epsilon-disc. The second condition expands convergence of the
  partial sums of pi times the squared radii. In the last condition, (a,b) and
  the nonzero direction (u,v) parametrize an arbitrary affine line, and the
  squared-distance inequality is equivalent, for nonnegative R(i), to that
  line meeting the closed disc centered at (X(i),Y(i)).

  The source solution proposition is annotated True, so its biconditional
  with this existence claim is rendered as the existence claim itself. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d L N R X Y a b e f i j n t u v x y $.

  putnambench-putnam-1991-a4 $a |-
    E. X e. ( RR ^m NN0 )
      E. Y e. ( RR ^m NN0 )
        E. R e. ( RR ^m NN0 )
          (
            A. i e. NN0 0 <_ ( R ` i )
            /\
            (
              -.
              E. x e. RR E. y e. RR
                A. e e. RR
                  (
                    0 < e
                    ->
                    E. f e. ( NN0 ^m NN0 )
                      (
                        A. i e. NN0 A. j e. NN0
                          (
                            i < j
                            ->
                            ( f ` i ) < ( f ` j )
                          )
                        /\
                        A. i e. NN0
                          (
                            (
                              (
                                ( X ` ( f ` i ) )
                                -
                                x
                              )
                              ^
                              2
                            )
                            +
                            (
                              (
                                ( Y ` ( f ` i ) )
                                -
                                y
                              )
                              ^
                              2
                            )
                          )
                          <
                          ( e ^ 2 )
                      )
                  )
              /\
              (
                E. L e. RR
                  A. e e. RR
                    (
                      0 < e
                      ->
                      E. N e. NN0
                        A. n e. NN0
                          (
                            N <_ n
                            ->
                            (
                              abs
                              `
                              (
                                (
                                  sum_ i e. ( 0 ... n )
                                    (
                                      _pi
                                      x.
                                      ( ( R ` i ) ^ 2 )
                                    )
                                )
                                -
                                L
                              )
                            )
                            < e
                          )
                    )
                /\
                A. a e. RR A. b e. RR
                  A. u e. RR A. v e. RR
                    (
                      (
                        u =/= 0
                        \/
                        v =/= 0
                      )
                      ->
                      E. i e. NN0 E. t e. RR
                        (
                          (
                            (
                              ( X ` i )
                              -
                              (
                                a
                                +
                                ( t x. u )
                              )
                            )
                            ^
                            2
                          )
                          +
                          (
                            (
                              ( Y ` i )
                              -
                              (
                                b
                                +
                                ( t x. v )
                              )
                            )
                            ^
                            2
                          )
                        )
                        <_
                        ( ( R ` i ) ^ 2 )
                    )
              )
            )
          )
  $.
$}
