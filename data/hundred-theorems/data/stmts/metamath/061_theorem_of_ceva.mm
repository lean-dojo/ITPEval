$(
  Statement-only formalization of Hundred Theorems item 061, Ceva's theorem.

  This reproduces set.mm theorem cevath in the complex-plane model of
  Euclidean geometry. The essential hypotheses state the required
  collinearities and nondegeneracy conditions; the conclusion is the
  multiplicative Ceva relation.
$)

$[ library/set.mm $]

${
  $d x y A $.
  $d x B y $.
  $d x C y $.
  $d x D y $.
  $d x O y $.
  $d x E y $.
  $d x F y $.

  hundred-theorems-061-oriented-area $e
    |- G =
       ( x e. CC , y e. CC |->
         ( Im ` ( ( * ` x ) x. y ) ) )
  $.
  hundred-theorems-061-triangle $e
    |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) )
  $.
  hundred-theorems-061-side-points $e
    |- ( ph -> ( F e. CC /\ D e. CC /\ E e. CC ) )
  $.
  hundred-theorems-061-concurrency-point $e
    |- ( ph -> O e. CC )
  $.
  hundred-theorems-061-concurrent $e
    |- (
         ph
         ->
         (
           ( ( A - O ) G ( D - O ) ) = 0
           /\
           ( ( B - O ) G ( E - O ) ) = 0
           /\
           ( ( C - O ) G ( F - O ) ) = 0
         )
       )
  $.
  hundred-theorems-061-on-sides $e
    |- (
         ph
         ->
         (
           ( ( A - F ) G ( B - F ) ) = 0
           /\
           ( ( B - D ) G ( C - D ) ) = 0
           /\
           ( ( C - E ) G ( A - E ) ) = 0
         )
       )
  $.
  hundred-theorems-061-nondegenerate $e
    |- (
         ph
         ->
         (
           ( ( A - O ) G ( B - O ) ) =/= 0
           /\
           ( ( B - O ) G ( C - O ) ) =/= 0
           /\
           ( ( C - O ) G ( A - O ) ) =/= 0
         )
       )
  $.

  hundred-theorems-061-ceva $a
    |- (
         ph
         ->
         (
           ( ( A - F ) x. ( C - E ) ) x. ( B - D )
         )
         =
         (
           ( ( F - B ) x. ( E - A ) ) x. ( D - C )
         )
       )
  $.
$}
