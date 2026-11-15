$(
  Statement-only formalization of "The Binomial Theorem" from Hundred
  Theorems item 044: in every commutative semiring, a natural power of a sum
  is the inclusive finite sum of the binomial coefficients times the
  corresponding powers of the two summands. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library supplies semirings, their carrier and
  operations, nonnegative integers, binomial coefficients, natural scalar
  multiplication, natural powers, and finite group sums. The hypotheses
  below are definitional abbreviations for the carrier and operations of R.
  Requiring the multiplicative monoid G to be commutative makes R a
  commutative semiring.

  The final $a assertion is unproved and adds no $p proof statement.
$)

${
  ht044.s $e |- S = ( Base ` R ) $.
  ht044.m $e |- .X. = ( .r ` R ) $.
  ht044.t $e |- .x. = ( .g ` R ) $.
  ht044.a $e |- .+ = ( +g ` R ) $.
  ht044.g $e |- G = ( mulGrp ` R ) $.
  ht044.e $e |- .^ = ( .g ` G ) $.

  $d A k $.  $d B k $.  $d N k $.  $d R k $.  $d S k $.
  $d .x. k $.  $d .X. k $.  $d .^ k $.  $d .+ k $.

  hundred-theorems-044-binomial $a
    |- ( ( ( R e. SRing /\ G e. CMnd /\ N e. NN0 )
             /\ ( A e. S /\ B e. S ) )
          -> ( N .^ ( A .+ B ) ) =
             ( R gsum ( k e. ( 0 ... N ) |->
                 ( ( N _C k ) .x.
                   ( ( k .^ A ) .X. ( ( N - k ) .^ B ) ) ) ) ) )
  $.
$}
