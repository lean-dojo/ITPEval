$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_a3: pi over two is the smallest positive real zero time
  attainable by globally differentiable real functions satisfying the
  stated coupled derivative bounds and initial conditions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P23A3Feasible r keeps the two total real functions existentially
  quantified. The domain conditions say that each function is
  differentiable at every real point, and the following restricted
  universal states both absolute-value derivative inequalities pointwise.

  The final conjunction is the attained-minimum expansion of the source
  problem: pi/2 is positive and feasible, and it is no greater than every
  other positive feasible real zero time. All declarations are unproved $a
  statement encodings; this database contains no $p proof declaration.
$)

$c P23A3Feasible $.

p23a3-feasible-syntax $a wff ( P23A3Feasible r ) $.

${
  $d f g r x $.

  p23a3-feasible-definition $a |- (
    ( P23A3Feasible r )
    <->
    E. f e. ( RR ^m RR )
      E. g e. ( RR ^m RR )
        (
          (
            RR C_ dom ( RR _D f )
            /\
            RR C_ dom ( RR _D g )
          )
          /\
          (
            (
              0 < ( f ` 0 )
              /\
              ( g ` 0 ) = 0
            )
            /\
            (
              A. x e. RR
                (
                  (
                    abs ` ( ( RR _D f ) ` x )
                  )
                  <_
                  ( abs ` ( g ` x ) )
                  /\
                  (
                    abs ` ( ( RR _D g ) ` x )
                  )
                  <_
                  ( abs ` ( f ` x ) )
                )
              /\
              ( f ` r ) = 0
            )
          )
        )
  ) $.
$}

putnambench-putnam-2023-a3 $a |- (
  (
    0 < ( _pi / 2 )
    /\
    ( P23A3Feasible ( _pi / 2 ) )
  )
  /\
  A. r e. RR
    (
      (
        0 < r
        /\
        ( P23A3Feasible r )
      )
      ->
      ( _pi / 2 ) <_ r
    )
) $.
