$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_b2: the maximum of the integral of f(x) / x on [1,3] for
  integrable real functions bounded between -1 and 1 with integral zero is
  the natural logarithm of 4 / 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is set.mm's class of total real-valued functions. Membership of
  the restricted mapping in L^1 states Lebesgue integrability on [1,3], and
  S. is the corresponding real Lebesgue integral. Closed rather than open
  interval endpoints do not change either integral.

  The first conjunct gives an admissible function attaining log(4/3), and
  the second says that every admissible function has weighted integral at
  most log(4/3). Thus the conjunction expands the source IsGreatest
  assertion. The declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d f x $.

  putnambench-putnam-2014-b2 $a |- (
    E. f e. ( RR ^m RR )
      (
        (
          (
            ( x e. ( 1 [,] 3 ) |-> ( f ` x ) ) e. L^1
            /\
            A. x e. ( 1 [,] 3 )
              (
                ( -u 1 ) <_ ( f ` x )
                /\
                ( f ` x ) <_ 1
              )
          )
          /\
          S. ( 1 [,] 3 ) ( f ` x ) _d x = 0
        )
        /\
        S. ( 1 [,] 3 ) ( ( f ` x ) / x ) _d x
          =
          ( log ` ( 4 / 3 ) )
      )
    /\
    A. f e. ( RR ^m RR )
      (
        (
          (
            ( x e. ( 1 [,] 3 ) |-> ( f ` x ) ) e. L^1
            /\
            A. x e. ( 1 [,] 3 )
              (
                ( -u 1 ) <_ ( f ` x )
                /\
                ( f ` x ) <_ 1
              )
          )
          /\
          S. ( 1 [,] 3 ) ( f ` x ) _d x = 0
        )
        ->
        S. ( 1 [,] 3 ) ( ( f ` x ) / x ) _d x
          <_
          ( log ` ( 4 / 3 ) )
      )
  ) $.
$}
