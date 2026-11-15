$(
  Statement-only formalization of "Stirling's Formula" from the Hundred
  Theorems corpus artifact 090 (hundred-theorems__metamath__090): the
  factorial sequence, normalized by sqrt(2 n) times (n/e)^n, converges to
  sqrt(pi). This file contains no proof.
$)

$[ library/set.mm $]

$(
  The assertion expands convergence over natural indices into its
  epsilon-threshold form. In set.mm, ! is factorial, _e is Euler's number,
  _pi is pi, and natural numbers are included in the real arithmetic used
  below. This is the normalized form of Stirling's formula and is
  definitionally equivalent to saying that n! is asymptotic to
  sqrt(2 pi n) times (n/e)^n. The final declaration is an unproved $a
  statement.
$)

hundred-theorems-090-stirling-formula $a
  |- A. e e. RR
       ( 0 < e ->
         E. m e. NN0
           A. n e. NN0
             ( m <_ n ->
               ( abs `
                 ( ( ( ! ` n ) /
                     ( ( sqrt ` ( 2 x. n ) ) x.
                       ( ( n / _e ) ^ n ) ) )
                   - ( sqrt ` _pi ) ) ) < e ) ) )
$.
