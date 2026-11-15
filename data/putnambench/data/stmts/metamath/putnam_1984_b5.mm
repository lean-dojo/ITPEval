$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1984_b5: the alternating mth-power sum weighted by binary digit
  parity equals (-1)^m times 2^(m(m-1)/2) times m factorial. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers and NN is its class of
  positive integers. The universally quantified function d is characterized
  by the source recurrence for the number of ones in a binary expansion:
  d(n) is n below two, and otherwise is n mod 2 plus d(floor(n/2)).

  The explicit Rocq solution and the Lean and Isabelle solution annotations
  give a = 2, f(x) = x(x-1)/2, and g(x) = x. Their evaluations at m are
  inlined in the right side. Thus the inclusive finite sum and its real-valued
  closed form preserve the source statement definitionally. The final
  declaration is a single unproved $a corpus statement; this database contains
  no $p proof declaration.
$)

${
  $d d k m n $.

  putnambench-putnam-1984-b5 $a |-
    A. d e. ( NN0 ^m NN0 )
      (
        A. n e. NN0
          ( d ` n )
          =
          if (
            n < 2 ,
            n ,
            (
              ( n mod 2 )
              +
              ( d ` ( |_ ` ( n / 2 ) ) )
            )
          )
        ->
        A. m e. NN
          (
            sum_ k e. ( 0 ... ( ( 2 ^ m ) - 1 ) )
              (
                ( ( -u 1 ) ^ ( d ` k ) )
                x.
                ( k ^ m )
              )
            =
            (
              ( ( -u 1 ) ^ m )
              x.
              (
                (
                  2
                  ^
                  (
                    ( m x. ( m - 1 ) )
                    /
                    2
                  )
                )
                x.
                ( ! ` m )
              )
            )
          )
      )
  $.
$}
