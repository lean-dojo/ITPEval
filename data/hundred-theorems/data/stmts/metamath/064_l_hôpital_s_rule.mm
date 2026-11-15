$(
  Statement-only formalization of Hundred Theorems item 064, L'Hopital's
  rule for a zero-over-zero limit.

  This reproduces set.mm theorem lhop. Both the derivative quotient and the
  original quotient are formed only on the punctured neighborhood D, so no
  artificial global nonzero-denominator requirement is introduced.
$)

$[ library/set.mm $]

${
  $d z B $.
  $d z C $.
  $d z D $.
  $d z F $.
  $d ph z $.
  $d z G $.
  $d z I $.

  hundred-theorems-064-domain $e
    |- ( ph -> A C_ RR )
  $.
  hundred-theorems-064-f $e
    |- ( ph -> F : A --> RR )
  $.
  hundred-theorems-064-g $e
    |- ( ph -> G : A --> RR )
  $.
  hundred-theorems-064-neighborhood $e
    |- ( ph -> I e. ( topGen ` ran (,) ) )
  $.
  hundred-theorems-064-limit-point $e
    |- ( ph -> B e. I )
  $.
  hundred-theorems-064-punctured-domain $e
    |- D = ( I \ { B } )
  $.
  hundred-theorems-064-f-differentiable $e
    |- ( ph -> D C_ dom ( RR _D F ) )
  $.
  hundred-theorems-064-g-differentiable $e
    |- ( ph -> D C_ dom ( RR _D G ) )
  $.
  hundred-theorems-064-f-zero-limit $e
    |- ( ph -> 0 e. ( F limCC B ) )
  $.
  hundred-theorems-064-g-zero-limit $e
    |- ( ph -> 0 e. ( G limCC B ) )
  $.
  hundred-theorems-064-g-nonzero $e
    |- ( ph -> -. 0 e. ( G " D ) )
  $.
  hundred-theorems-064-g-derivative-nonzero $e
    |- ( ph -> -. 0 e. ( ( RR _D G ) " D ) )
  $.
  hundred-theorems-064-derivative-ratio-limit $e
    |- (
         ph
         ->
         C e.
           (
             (
               z e. D |->
               ( ( ( RR _D F ) ` z ) / ( ( RR _D G ) ` z ) )
             )
             limCC B
           )
       )
  $.

  hundred-theorems-064-lhopital $a
    |- (
         ph
         ->
         C e.
           (
             ( z e. D |-> ( ( F ` z ) / ( G ` z ) ) )
             limCC B
           )
       )
  $.
$}
