$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_a6: the greatest real lower bound of the integral of
  |f'(x) - f(x)| over the unit interval, among continuously differentiable
  real functions with f(0) = 0 and f(1) = 1, is 1 / exp(1). This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions. Membership of its
  restriction to [0,1] in the order-one C^n class is set.mm's native
  formulation of continuous differentiability on that closed interval.
  On the open interval (0,1), the ordinary real derivative RR _D F agrees
  with the derivative of the restriction. Using the open interval in the
  Lebesgue integral is equivalent to the endpoint-inclusive source integral.

  The two conjuncts in the final assertion expand IsGreatest: 1 / exp(1)
  is a lower bound for every admissible function, and every real number with
  that lower-bound property is at most 1 / exp(1). The declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d f u x $.

  putnambench-putnam-1980-a6 $a |- (
    (
      A. f e. ( RR ^m RR )
        (
          (
            (
              ( f |` ( 0 [,] 1 ) )
              e. ( ( C^n ` ( 0 [,] 1 ) ) ` 1 )
              /\
              ( f ` 0 ) = 0
            )
            /\
            ( f ` 1 ) = 1
          )
          ->
          ( 1 / ( exp ` 1 ) )
          <_
          S. ( 0 (,) 1 )
            (
              abs `
                (
                  ( ( RR _D f ) ` x )
                  -
                  ( f ` x )
                )
            )
            _d x
        )
      /\
      A. u e. RR
        (
          (
            A. f e. ( RR ^m RR )
              (
                (
                  (
                    ( f |` ( 0 [,] 1 ) )
                    e. ( ( C^n ` ( 0 [,] 1 ) ) ` 1 )
                    /\
                    ( f ` 0 ) = 0
                  )
                  /\
                  ( f ` 1 ) = 1
                )
                ->
                u
                <_
                S. ( 0 (,) 1 )
                  (
                    abs `
                      (
                        ( ( RR _D f ) ` x )
                        -
                        ( f ` x )
                      )
                  )
                  _d x
              )
          )
          ->
          u <_ ( 1 / ( exp ` 1 ) )
        )
    )
  ) $.
$}
