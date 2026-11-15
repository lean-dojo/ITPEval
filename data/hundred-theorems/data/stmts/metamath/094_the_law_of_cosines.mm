$(
  Statement-only formalization of Hundred Theorems item 094, the law of
  cosines.

  This reproduces set.mm theorem lawcos in the complex-plane model of
  Euclidean geometry. X, Y, and Z are the side lengths and O is the included
  angle at C.
$)

$[ library/set.mm $]

${
  $d x y A $.
  $d x B y $.
  $d x C y $.

  hundred-theorems-094-angle $e
    |- F =
       ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |->
         ( Im ` ( log ` ( y / x ) ) ) )
  $.
  hundred-theorems-094-x $e
    |- X = ( abs ` ( B - C ) )
  $.
  hundred-theorems-094-y $e
    |- Y = ( abs ` ( A - C ) )
  $.
  hundred-theorems-094-z $e
    |- Z = ( abs ` ( A - B ) )
  $.
  hundred-theorems-094-o $e
    |- O = ( ( B - C ) F ( A - C ) )
  $.

  hundred-theorems-094-law-of-cosines $a
    |- (
         (
           ( A e. CC /\ B e. CC /\ C e. CC )
           /\
           ( A =/= C /\ B =/= C )
         )
         ->
         ( Z ^ 2 )
         =
         (
           ( ( X ^ 2 ) + ( Y ^ 2 ) )
           -
           ( 2 x. ( ( X x. Y ) x. ( cos ` O ) ) )
         )
       )
  $.
$}
