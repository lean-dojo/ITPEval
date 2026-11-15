$(
  Statement-only formalization of "Sum of an Arithmetic Series" from Hundred
  Theorems corpus artifact 068: in every semiring, the inclusive finite sum of
  an arithmetic progression equals its standard expression using natural
  multiples and the triangular number. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library supplies semirings, their carriers and additive
  operations, nonnegative integers, natural scalar multiplication, and finite
  group sums. The hypotheses below are definitional abbreviations for the
  carrier and additive operations of R.

  The expression ` sum_ j e. ( 0 ... N ) j ` is the triangular-number
  coefficient. The map expression in ` R gsum ` binds k and sums
  ` A .+ ( k .x. D ) ` from k = 0 through k = N in the additive commutative
  monoid of R. Thus the assertion is valid for an arbitrary semiring and
  specializes to the natural-number statements in the other sources.

  The final $a assertion is unproved and adds no $p proof statement.
$)

${
  ht068.s $e |- S = ( Base ` R ) $.
  ht068.t $e |- .x. = ( .g ` R ) $.
  ht068.a $e |- .+ = ( +g ` R ) $.

  $d j k $.
  $d A j $.  $d D j $.  $d N j $.  $d R j $.  $d S j $.
  $d .x. j $.  $d .+ j $.
  $d A k $.  $d D k $.  $d N k $.  $d R k $.  $d S k $.
  $d .x. k $.  $d .+ k $.

  hundred-theorems-068-arithmetic-series $a
    |- ( ( ( R e. SRing /\ N e. NN0 )
             /\ ( A e. S /\ D e. S ) )
          -> ( ( ( N + 1 ) .x. A )
                 .+ ( ( sum_ j e. ( 0 ... N ) j ) .x. D ) ) =
             ( R gsum ( k e. ( 0 ... N ) |->
                 ( A .+ ( k .x. D ) ) ) ) )
  $.
$}
