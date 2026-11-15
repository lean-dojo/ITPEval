$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_b4: the least nonnegative time for a continuous real function
  with prescribed one-sided derivative limits and piecewise constant second
  derivative to reach 2023 is 29. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A in RR ^m NN0 is the arbitrary real sequence (t_k), and F in RR ^m RR
  is an arbitrary total real extension of the function defined on
  [t_0,+infinity). P23B4RightLimit(F,a) is the epsilon-delta expansion of
  the right-hand limit F'(x) -> 0 as x -> a, with membership in the
  derivative domain made explicit.

  P23B4Data(n,A,F) states the unit spacing of consecutive sequence entries,
  continuity on the closed half-line from t_0, twice differentiability at
  every point above t_0 except t_1 through t_n, the initial value 1/2, all
  right-hand derivative limits, and the specified piecewise values of the
  second derivative. The entries 1 and 2 of ( RR Dn F ) are set.mm's first
  and second real derivatives.

  P23B4Admissible(T) keeps n, A, and F internally existentially quantified
  and adds T >= 0 and F(t_0 + T) = 2023. The final conjunction expands
  IsLeast: 29 is admissible and is no greater than every admissible real T.
  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c P23B4RightLimit P23B4Data P23B4Admissible $.

p23b4-right-limit-syntax $a wff ( P23B4RightLimit F a ) $.
p23b4-data-syntax $a wff ( P23B4Data n A F ) $.
p23b4-admissible-syntax $a wff ( P23B4Admissible T ) $.

${
  $d F a d e x $.

  p23b4-right-limit-definition $a |- (
    ( P23B4RightLimit F a )
    <->
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
                  a < x
                  /\
                  ( x - a ) < d
                )
                ->
                (
                  x e. dom ( ( RR Dn F ) ` 1 )
                  /\
                  (
                    abs
                    `
                    ( ( ( RR Dn F ) ` 1 ) ` x )
                  )
                  < e
                )
              )
          )
      )
  ) $.
$}

${
  $d A F a k n x $.

  p23b4-data-definition $a |- (
    ( P23B4Data n A F )
    <->
    (
      (
        n e. NN0
        /\
        A e. ( RR ^m NN0 )
        /\
        F e. ( RR ^m RR )
      )
      /\
      A. k e. NN0
        (
          k < n
          ->
          (
            ( A ` k ) + 1
          )
          <_
          ( A ` ( k + 1 ) )
        )
      /\
      (
        F
        |`
        { x e. RR | ( A ` 0 ) <_ x }
      )
      e.
      (
        { x e. RR | ( A ` 0 ) <_ x }
        -cn->
        RR
      )
      /\
      A. x e. RR
        (
          (
            ( A ` 0 ) < x
            /\
            A. k e. NN0
              (
                (
                  0 < k
                  /\
                  k <_ n
                )
                ->
                x =/= ( A ` k )
              )
          )
          ->
          (
            x e. dom ( ( RR Dn F ) ` 1 )
            /\
            x e. dom ( ( RR Dn F ) ` 2 )
          )
        )
      /\
      ( F ` ( A ` 0 ) ) = ( 1 / 2 )
      /\
      A. k e. NN0
        (
          k <_ n
          ->
          ( P23B4RightLimit F ( A ` k ) )
        )
      /\
      A. k e. NN0
        (
          k < n
          ->
          A. x e. RR
            (
              (
                ( A ` k ) < x
                /\
                x < ( A ` ( k + 1 ) )
              )
              ->
              (
                ( ( ( RR Dn F ) ` 2 ) ` x )
                =
                ( k + 1 )
              )
            )
        )
      /\
      A. x e. RR
        (
          ( A ` n ) < x
          ->
          (
            ( ( ( RR Dn F ) ` 2 ) ` x )
            =
            ( n + 1 )
          )
        )
    )
  ) $.
$}

${
  $d A F T n $.

  p23b4-admissible-definition $a |- (
    ( P23B4Admissible T )
    <->
    (
      T e. RR
      /\
      0 <_ T
      /\
      E. n e. NN0
        E. A e. ( RR ^m NN0 )
          E. F e. ( RR ^m RR )
            (
              ( P23B4Data n A F )
              /\
              (
                F
                `
                (
                  ( A ` 0 )
                  +
                  T
                )
              )
              =
              ( ; ; ; 2 0 2 3 )
            )
    )
  ) $.
$}

putnambench-putnam-2023-b4 $a |- (
  ( P23B4Admissible ; 2 9 )
  /\
  A. T e. RR
    (
      ( P23B4Admissible T )
      ->
      ; 2 9 <_ T
    )
) $.
