$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_a2 (putnambench__metamath__putnam_2025_a2): the greatest real
  lower coefficient and least real upper coefficient bounding sin(x) by
  scalar multiples of x(pi-x) on [0,pi] are 1/pi and 4/pi^2. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The left side of the biconditional inlines the annotated solution pair.
  On the right, each first universal clause states that the displayed
  coefficient is admissible on the full closed real interval [0,pi]. The
  following universal clause compares it with every other admissible real
  coefficient, explicitly expanding the source IsGreatest and IsLeast
  predicates.

  Thus all real domains, interval quantifiers, inequalities, and extremal
  quantifier scopes are retained. The final declaration is a single
  unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d a b c d x $.

  putnambench-putnam-2025-a2 $a |- A. a e. RR A. b e. RR
    (
      (
        a = ( 1 / _pi )
        /\
        b = ( 4 / ( _pi ^ 2 ) )
      )
      <->
      (
        (
          A. x e. ( 0 [,] _pi )
            (
              ( ( a x. x ) x. ( _pi - x ) )
              <_
              ( sin ` x )
            )
          /\
          A. c e. RR
            (
              (
                A. x e. ( 0 [,] _pi )
                  (
                    ( ( c x. x ) x. ( _pi - x ) )
                    <_
                    ( sin ` x )
                  )
              )
              ->
              c <_ a
            )
        )
        /\
        (
          A. x e. ( 0 [,] _pi )
            (
              ( sin ` x )
              <_
              ( ( b x. x ) x. ( _pi - x ) )
            )
          /\
          A. d e. RR
            (
              (
                A. x e. ( 0 [,] _pi )
                  (
                    ( sin ` x )
                    <_
                    ( ( d x. x ) x. ( _pi - x ) )
                  )
              )
              ->
              b <_ d
            )
        )
      )
    )
  $.
$}
