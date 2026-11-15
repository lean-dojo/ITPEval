$(
  Statement-only formalization of Hundred Theorems item 065, the isosceles
  triangle theorem.

  This reproduces set.mm theorem isosctr in its complex-plane geometry. If A
  and B are equidistant from C, the two base angles are equal.
$)

$[ library/set.mm $]

${
  $d x y A $.
  $d x B y $.
  $d x C y $.

  hundred-theorems-065-angle $e
    |- F =
       ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |->
         ( Im ` ( log ` ( y / x ) ) ) )
  $.

  hundred-theorems-065-isosceles $a
    |- (
         (
           ( A e. CC /\ B e. CC /\ C e. CC )
           /\
           ( A =/= C /\ B =/= C /\ A =/= B )
           /\
           ( abs ` ( A - C ) ) = ( abs ` ( B - C ) )
         )
         ->
         (
           ( C - A ) F ( B - A )
         )
         =
         (
           ( A - B ) F ( C - B )
         )
       )
  $.
$}
