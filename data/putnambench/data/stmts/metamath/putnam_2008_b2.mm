$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_b2: the factorial-scaled values at one of the recursively
  integrated natural-logarithm functions converge, after division by the
  logarithm of the index, to negative one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  f ranges over all NN0-indexed families of total real-valued functions.
  Its zeroth member is the real part of the complex logarithm away from zero
  and is explicitly zero at zero, matching Lean's total Real.log. For every
  nonnegative integer n and positive real x, its next member at x is the real
  Lebesgue integral of the nth member over the open interval (0,x). Endpoint
  inclusion does not affect this integral.

  The conclusion expands convergence over natural indices into its
  epsilon-threshold form. Set.mm's ! and S. binder are factorial and real
  Lebesgue integration, respectively; Re(log x) is the total real natural
  logarithm. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d e f m n t x $.

  putnambench-putnam-2008-b2 $a |- A. f e.
    ( ( RR ^m RR ) ^m NN0 )
    (
      (
        A. x e. RR
          ( ( f ` 0 ) ` x )
          =
          if ( x = 0 , 0 , ( Re ` ( log ` x ) ) )
        /\
        A. n e. NN0 A. x e. RR
          (
            0 < x
            ->
            ( ( f ` ( n + 1 ) ) ` x )
            =
            S. ( 0 (,) x )
              ( ( f ` n ) ` t )
              _d t
          )
      )
      ->
      A. e e. RR
        (
          0 < e
          ->
          E. m e. NN0
            A. n e. NN0
              (
                m <_ n
                ->
                (
                  abs
                  `
                  (
                    (
                      (
                        ( ! ` n )
                        x.
                        ( ( f ` n ) ` 1 )
                      )
                      /
                      ( Re ` ( log ` n ) )
                    )
                    -
                    ( -u 1 )
                  )
                )
                < e
              )
        )
    )
  $.
$}
