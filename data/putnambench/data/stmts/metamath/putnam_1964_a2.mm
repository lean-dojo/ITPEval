$(
  Statement-only formalization of PutnamBench artifact putnam_1964_a2:
  no positive continuous real-valued function on the closed unit interval
  has zeroth, first, and second moments 1, A, and A^2 respectively. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over total real-valued functions. Its restriction to [0,1] is
  required to be continuous in set.mm's native function-space notation.
  Continuity on the compact interval makes F, x F(x), and x^2 F(x)
  integrable, so the three Lebesgue integrals encode the published moments.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A F x $.

  putnambench-putnam-1964-a2 $a |- A. A e. RR
    -. E. F e. ( RR ^m RR )
      (
        (
          ( F |` ( 0 [,] 1 ) )
          e.
          ( ( 0 [,] 1 ) -cn-> RR )
        )
        /\
        (
          A. x e. ( 0 [,] 1 )
            0 < ( F ` x )
        )
        /\
        (
          S. ( 0 [,] 1 ) ( F ` x ) _d x
        )
        =
        1
        /\
        (
          S. ( 0 [,] 1 )
            ( x x. ( F ` x ) )
            _d x
        )
        =
        A
        /\
        (
          S. ( 0 [,] 1 )
            ( ( x ^ 2 ) x. ( F ` x ) )
            _d x
        )
        =
        ( A ^ 2 )
      )
  $.
$}
