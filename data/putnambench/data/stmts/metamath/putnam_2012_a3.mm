$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_a3: the unique continuous real function on the closed interval
  from negative one to one satisfying the given functional equation,
  normalization at zero, and finite left-limit condition is
  sqrt(1 - x^2). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P12A3Solution is the total real function x |-> sqrt(1 - x^2), using zero
  when the radicand is negative, as do the total real square-root operations
  in the source formalizations. Only its values on [-1,1] occur in the
  conclusion and in the active neighborhood of the left-limit condition.

  P12A3Satisfies requires a total real-valued function, continuity of its
  restriction to [-1,1], the source functional equation at every point of
  that interval, and normalization at zero. Its final conjunct is the
  epsilon-delta expansion of existence of a finite real left-hand limit at
  one for f(x) / sqrt(1-x); the limit and all cutoffs remain internally
  quantified.

  The final assertion states both that the displayed closed form satisfies
  every condition and that every satisfying function agrees with it
  throughout [-1,1]. All declarations are unproved $a statement encodings;
  this database contains no $p proof declaration.
$)

$c P12A3Solution P12A3Satisfies $.

p12a3-solution-syntax $a class P12A3Solution $.
p12a3-satisfies-syntax $a wff ( P12A3Satisfies F ) $.

p12a3-solution-definition $a |- P12A3Solution =
  (
    x e. RR |->
      if (
        0 <_ ( 1 - ( x ^ 2 ) ) ,
        ( sqrt ` ( 1 - ( x ^ 2 ) ) ) ,
        0
      )
  )
$.

${
  $d F L d e x $.

  p12a3-satisfies-definition $a |- (
    ( P12A3Satisfies F )
    <->
    (
      F e. ( RR ^m RR )
      /\
      (
        ( F |` ( ( -u 1 ) [,] 1 ) )
        e.
        ( ( ( -u 1 ) [,] 1 ) -cn-> RR )
      )
      /\
      A. x e. ( ( -u 1 ) [,] 1 )
        (
          ( F ` x )
          =
          (
            (
              ( 2 - ( x ^ 2 ) )
              /
              2
            )
            x.
            (
              F
              `
              (
                ( x ^ 2 )
                /
                ( 2 - ( x ^ 2 ) )
              )
            )
          )
        )
      /\
      ( F ` 0 ) = 1
      /\
      E. L e. RR
        A. e e. RR
          (
            0 < e
            ->
            E. d e. RR
              (
                0 < d
                /\
                A. x e. RR
                  (
                    (
                      x < 1
                      /\
                      ( abs ` ( x - 1 ) ) < d
                    )
                    ->
                    (
                      abs
                      `
                      (
                        (
                          ( F ` x )
                          /
                          ( sqrt ` ( 1 - x ) )
                        )
                        -
                        L
                      )
                    )
                    < e
                  )
              )
          )
    )
  ) $.
$}

${
  $d F x $.

  putnambench-putnam-2012-a3 $a |- (
    ( P12A3Satisfies P12A3Solution )
    /\
    A. F e. ( RR ^m RR )
      (
        ( P12A3Satisfies F )
        ->
        A. x e. ( ( -u 1 ) [,] 1 )
          ( F ` x ) = ( P12A3Solution ` x )
      )
  ) $.
$}
