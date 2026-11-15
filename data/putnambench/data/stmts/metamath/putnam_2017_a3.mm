$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_a3: strict increase and divergence to positive infinity of
  the integral sequence formed from two distinct positive continuous
  real functions with equal integrals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F and G range over all total real-valued functions, and I ranges over all
  real sequences indexed by NN0. Their restrictions to [a,b] are continuous,
  both functions are positive there, their integrals over (a,b) agree, and
  they differ at some point of [a,b].

  For every positive natural n, the displayed integral defines I(n). The
  second conclusion is the threshold definition of I tending to positive
  infinity: every real lower bound M is eventually exceeded by every term.
  This is equivalent to Tendsto I atTop atTop for a real sequence on NN0.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F G I M N a b n x $.

  putnambench-putnam-2017-a3 $a |-
    A. a e. RR
      A. b e. RR
        A. F e. ( RR ^m RR )
          A. G e. ( RR ^m RR )
            A. I e. ( RR ^m NN0 )
              (
                (
                  (
                    (
                      (
                        (
                          a < b
                          /\
                          ( F |` ( a [,] b ) )
                            e. ( ( a [,] b ) -cn-> RR )
                        )
                        /\
                        ( G |` ( a [,] b ) )
                          e. ( ( a [,] b ) -cn-> RR )
                      )
                      /\
                      A. x e. ( a [,] b )
                        ( 0 < ( F ` x ) /\ 0 < ( G ` x ) )
                    )
                    /\
                    (
                      S. ( a (,) b ) ( F ` x ) _d x
                      =
                      S. ( a (,) b ) ( G ` x ) _d x
                    )
                  )
                  /\
                  E. x e. ( a [,] b ) ( F ` x ) =/= ( G ` x )
                )
                /\
                A. n e. NN
                  ( I ` n )
                  =
                  S. ( a (,) b )
                    (
                      ( ( F ` x ) ^ ( n + 1 ) )
                      /
                      ( ( G ` x ) ^ n )
                    )
                    _d x
              )
              ->
              (
                A. n e. NN
                  ( I ` n ) < ( I ` ( n + 1 ) )
                /\
                A. M e. RR
                  E. N e. NN0
                    A. n e. NN0
                      (
                        N <_ n
                        ->
                        M < ( I ` n )
                      )
              )
  $.
$}
