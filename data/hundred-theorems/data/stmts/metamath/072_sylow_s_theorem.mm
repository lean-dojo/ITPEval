$(
  Statement-only formalization of Hundred Theorems item 072, the existence
  part of Sylow's theorem.

  This is the proposition proved by set.mm theorem sylow1: if P^N divides the
  order of a finite group G, then G has a subgroup of order P^N.
$)

$[ library/set.mm $]

${
  $d g N $.
  $d g X $.
  $d g G $.
  $d P g $.
  $d ph g $.

  hundred-theorems-072-group-carrier $e
    |- X = ( Base ` G )
  $.
  hundred-theorems-072-group $e
    |- ( ph -> G e. Grp )
  $.
  hundred-theorems-072-finite $e
    |- ( ph -> X e. Fin )
  $.
  hundred-theorems-072-prime $e
    |- ( ph -> P e. Prime )
  $.
  hundred-theorems-072-exponent $e
    |- ( ph -> N e. NN0 )
  $.
  hundred-theorems-072-divides-order $e
    |- ( ph -> ( P ^ N ) || ( # ` X ) )
  $.

  hundred-theorems-072-sylow-existence $a
    |- (
         ph
         ->
         E. g e. ( SubGrp ` G ) ( # ` g ) = ( P ^ N )
       )
  $.
$}
