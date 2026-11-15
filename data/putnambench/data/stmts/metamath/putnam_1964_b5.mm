$(
  Statement-only formalization of PutnamBench artifact putnam_1964_b5:
  convergence of the real reciprocal series of the successive least common
  multiples of a strictly increasing positive-integer sequence. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A and B are arbitrary nonnegative-integer-valued sequences indexed by NN0.
  The antecedent states that A is positive and strictly increasing, that
  B(0) = A(0), and that each successor value of B is the least common
  multiple of the preceding value and the next value of A.

  The conclusion existentially quantifies the real limit L and expands
  convergence of the reciprocal partial sums in epsilon-threshold form.
  For N in NN0, 0 ..^ N indexes exactly 0, ..., N - 1, matching the source
  partial sums. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d A B L N e i j k m n $.

  putnambench-putnam-1964-b5 $a
    |- A. A e. ( NN0 ^m NN0 )
         A. B e. ( NN0 ^m NN0 )
           (
             (
               (
                 A. i e. NN0 0 < ( A ` i )
                 /\
                 A. i e. NN0 A. j e. NN0
                   (
                     i < j
                     ->
                     ( A ` i ) < ( A ` j )
                   )
               )
               /\
               (
                 ( B ` 0 ) = ( A ` 0 )
                 /\
                 A. n e. NN0
                   ( B ` ( n + 1 ) )
                   =
                   (
                     ( B ` n )
                     lcm
                     ( A ` ( n + 1 ) )
                   )
               )
             )
             ->
             E. L e. RR
               A. e e. RR
                 (
                   0 < e
                   ->
                   E. m e. NN0
                     A. N e. NN0
                       (
                         m <_ N
                         ->
                         (
                           abs
                           `
                           (
                             (
                               sum_ k e. ( 0 ..^ N )
                                 ( 1 / ( B ` k ) )
                             )
                             -
                             L
                           )
                         )
                         < e
                       )
                 )
           )
  $.
$}
