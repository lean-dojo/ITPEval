$(
  Statement-only formalization of Hundred Theorems item 069, correctness of
  the Euclidean greatest-common-divisor algorithm.

  This is the proposition proved by set.mm theorem eucalg. E is one Euclidean
  transition and R is the resulting iteration sequence; after N steps its
  first component is gcd(M,N).
$)

$[ library/set.mm $]

${
  $d x y M $.
  $d x N y $.
  $d x A y $.
  $d x R $.

  hundred-theorems-069-step $e
    |- E =
       ( x e. NN0 , y e. NN0 |->
         if ( y = 0 , <. x , y >. , <. y , ( x mod y ) >. ) )
  $.
  hundred-theorems-069-run $e
    |- R = seq 0 ( ( E o. 1st ) , ( NN0 X. { A } ) )
  $.
  hundred-theorems-069-input $e
    |- A = <. M , N >.
  $.

  hundred-theorems-069-euclidean-algorithm $a
    |- (
         ( M e. NN0 /\ N e. NN0 )
         ->
         ( 1st ` ( R ` N ) ) = ( M gcd N )
       )
  $.
$}
