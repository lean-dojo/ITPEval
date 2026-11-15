$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_b1: positive integers h and k admit, for every positive real
  epsilon, positive integers m and n whose square-root linear combination
  has absolute value strictly between epsilon and twice epsilon. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers. Its positive square-root
  function on NN agrees with the nonnegative real square root, and complex
  absolute value on the resulting real expression agrees with real absolute
  value. Thus quantifying h, k, m, and n over NN is equivalent to the source
  integer variables together with their strict positivity conditions.

  The epsilon quantifier remains over all positive reals, and both integer
  witnesses remain internal to its scope. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d e h k m n $.

  putnambench-putnam-2011-b1 $a |- A. h e. NN A. k e. NN
    A. e e. RR
      (
        0 < e
        ->
        E. m e. NN E. n e. NN
          (
            e
            <
            (
              abs
              `
              (
                ( h x. ( sqrt ` m ) )
                -
                ( k x. ( sqrt ` n ) )
              )
            )
            /\
            (
              abs
              `
              (
                ( h x. ( sqrt ` m ) )
                -
                ( k x. ( sqrt ` n ) )
              )
            )
            <
            ( 2 x. e )
          )
      )
  $.
$}
