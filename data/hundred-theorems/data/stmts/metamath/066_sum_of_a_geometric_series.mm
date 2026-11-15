$(
  Statement-only formalization of Hundred Theorems item 066, the finite
  geometric-series formula.

  This reproduces set.mm theorem geoser for a complex ratio A distinct from
  one and a nonnegative number N of terms.
$)

$[ library/set.mm $]

${
  $d A k $.
  $d k N $.
  $d ph k $.

  hundred-theorems-066-ratio $e
    |- ( ph -> A e. CC )
  $.
  hundred-theorems-066-nonunit $e
    |- ( ph -> A =/= 1 )
  $.
  hundred-theorems-066-length $e
    |- ( ph -> N e. NN0 )
  $.

  hundred-theorems-066-geometric-series $a
    |- (
         ph
         ->
         sum_ k e. ( 0 ... ( N - 1 ) ) ( A ^ k )
         =
         ( ( 1 - ( A ^ N ) ) / ( 1 - A ) )
       )
  $.
$}
