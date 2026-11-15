$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/euler002_Solve_fqtvc: the Euler 2 verification condition initializes
  the even-Fibonacci summation loop and specifies both its advancing and
  terminating branches over the integers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A is the source integer parameter m. B, C, and D represent respectively
  Fibonacci.fib, FibSumEven.fib_sum_even, and FibOnlyEven.fib_even as total
  integer functions; C is represented extensionally as a function on ordered
  integer pairs. The scoped essential hypotheses reproduce the complete source
  equations: Fibonacci recursion on nonnegative indices, the zero and three
  conditional recurrence laws for the even-Fibonacci sum, and
  fib_even(n) = fib(3*n). Since the only remainder test is equality with zero
  modulo the positive integer 2, SetMM's mod test is equivalent to the source
  truncating-remainder test.

  NTP4VCStep renders the proposition-valued source conditional as two
  exhaustive guarded cases. Its existential witness remains internal to the
  false branch. The final declaration retains every explicit initialization
  conjunct, the full integer quantifiers over k and n, all loop hypotheses,
  and both branch conclusions. It is Metamath's native unproved $a statement
  encoding; this database contains no artifact-level $p declaration.
$)

$c NTP4VCStep $.

ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F ) $.

${
  $d q A B C D E F $.

  ntp4vc-step-definition $a |- (
    ( NTP4VCStep A B C D E F )
    <->
    (
      (
        ( D ` F ) <_ A
        /\
        (
          (
            (
              0 <_ ( A - ( D ` F ) )
              /\
              (
                A - ( D ` ( F + 1 ) )
              ) < ( A - ( D ` F ) )
            )
            /\
            (
              0 <_ ( F + 1 )
              /\
              (
                0 <_ ( E + 3 )
                /\
                (
                  ( D ` ( F + 1 ) ) = ( B ` ( E + 3 ) )
                  /\
                  (
                    (
                      ( 4 x. ( D ` ( F + 1 ) ) )
                      +
                      ( D ` F )
                    ) = ( D ` ( ( F + 1 ) + 1 ) )
                    /\
                    (
                      (
                        (
                          ( 4 x. ( D ` ( F + 1 ) ) )
                          +
                          ( D ` F )
                        ) = ( B ` ( ( E + 3 ) + 3 ) )
                        /\
                        (
                          (
                            C ` <. A , E >.
                          )
                          +
                          ( D ` F )
                        ) = (
                          C ` <. A , ( E + 3 ) >.
                        )
                      )
                      /\
                      (
                        0 <_ ( D ` ( F + 1 ) )
                        /\
                        ( D ` ( F + 1 ) )
                        <
                        (
                          ( 4 x. ( D ` ( F + 1 ) ) )
                          +
                          ( D ` F )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
      \/
      (
        -. ( D ` F ) <_ A
        /\
        E. q e. ZZ
          (
            (
              C ` <. A , E >.
            ) = (
              C ` <. A , q >.
            )
            /\
            A < ( B ` q )
          )
      )
    )
  ) $.
$}

${
  $d k n x y A B C D $.

  $( Source functions fib, fib_sum_even, and fib_even. $)
  ntp4vc-fib-function
    $e |- B e. ( ZZ ^m ZZ ) $.
  ntp4vc-fib-sum-even-function
    $e |- C e. ( ZZ ^m ( ZZ X. ZZ ) ) $.
  ntp4vc-fib-even-function
    $e |- D e. ( ZZ ^m ZZ ) $.

  ntp4vc-fib-definition $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      ( B ` x ) = if (
        x = 0 ,
        0 ,
        if (
          x = 1 ,
          1 ,
          (
            ( B ` ( x - 1 ) )
            +
            ( B ` ( x - 2 ) )
          )
        )
      )
    ) $.

  ntp4vc-fib-sum-even-zero $e |- A. y e. ZZ
    (
      C ` <. y , 0 >.
    ) = 0 $.

  ntp4vc-fib-sum-even-le $e |- A. x e. ZZ A. y e. ZZ
    (
      (
        0 <_ x
        /\
        (
          ( B ` x ) <_ y
          /\
          ( ( B ` x ) mod 2 ) = 0
        )
      )
      ->
      (
        C ` <. y , ( x + 1 ) >.
      ) = (
        (
          C ` <. y , x >.
        )
        +
        ( B ` x )
      )
    ) $.

  ntp4vc-fib-sum-even-gt $e |- A. x e. ZZ A. y e. ZZ
    (
      (
        0 <_ x
        /\
        (
          y < ( B ` x )
          /\
          ( ( B ` x ) mod 2 ) = 0
        )
      )
      ->
      (
        C ` <. y , ( x + 1 ) >.
      ) = (
        C ` <. y , x >.
      )
    ) $.

  ntp4vc-fib-sum-even-odd $e |- A. x e. ZZ A. y e. ZZ
    (
      (
        0 <_ x
        /\
        ( ( B ` x ) mod 2 ) =/= 0
      )
      ->
      (
        C ` <. y , ( x + 1 ) >.
      ) = (
        C ` <. y , x >.
      )
    ) $.

  ntp4vc-fib-even-definition $e |- A. x e. ZZ
    (
      D ` x
    ) = (
      B ` ( 3 x. x )
    ) $.

  $( Source theorem parameter A=m and assumption fact0. $)
  ntp4vc-m-integer $e |- A e. ZZ $.
  ntp4vc-fact0 $e |- 0 <_ A $.

  ntp4vc-pearl-euler002-solve-vc $a |- (
    0 <_ 0
    /\
    (
      0 <_ 0
      /\
      (
        0 = ( D ` 0 )
        /\
        (
          0 = ( B ` 0 )
          /\
          (
            2 = ( D ` ( 0 + 1 ) )
            /\
            (
              2 = ( B ` ( 0 + 3 ) )
              /\
              (
                0 = ( C ` <. A , 0 >. )
                /\
                (
                  0 <_ 0
                  /\
                  (
                    0 < 2
                    /\
                    A. k e. ZZ A. n e. ZZ
                      (
                        (
                          0 <_ n
                          /\
                          (
                            0 <_ k
                            /\
                            (
                              ( D ` n ) = ( B ` k )
                              /\
                              (
                                ( D ` ( n + 1 ) )
                                =
                                ( B ` ( k + 3 ) )
                                /\
                                (
                                  0 <_ ( D ` n )
                                  /\
                                  ( D ` n ) < ( D ` ( n + 1 ) )
                                )
                              )
                            )
                          )
                        )
                        ->
                        ( NTP4VCStep A B C D k n )
                      )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}
