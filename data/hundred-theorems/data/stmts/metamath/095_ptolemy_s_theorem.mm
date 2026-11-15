$(
  Statement-only formalization of Hundred Theorems item 095, Ptolemy's
  theorem.

  This is set.mm theorem ptolemy in its standard trigonometric form. For four
  cyclic arc angles summing to pi, it is equivalent to the product-sum
  relation among the corresponding chord lengths.
$)

$[ library/set.mm $]

hundred-theorems-095-ptolemy $a
  |- (
       (
         ( A e. CC /\ B e. CC )
         /\
         ( C e. CC /\ D e. CC )
         /\
         ( ( A + B ) + ( C + D ) ) = _pi
       )
       ->
       (
         ( ( sin ` A ) x. ( sin ` B ) )
         +
         ( ( sin ` C ) x. ( sin ` D ) )
       )
       =
       (
         ( sin ` ( B + C ) )
         x.
         ( sin ` ( A + C ) )
       )
     )
$.
