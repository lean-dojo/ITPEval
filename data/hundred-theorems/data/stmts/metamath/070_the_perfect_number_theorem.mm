$(
  Statement-only formalization of Hundred Theorems item 070, the
  Euclid-Euler characterization of even perfect numbers.

  This is the proposition proved by set.mm theorem perfect.
$)

$[ library/set.mm $]

${
  $d N p $.

  hundred-theorems-070-perfect-numbers $a
    |- (
         ( N e. NN /\ 2 || N )
         ->
         (
           ( 1 sigma N ) = ( 2 x. N )
           <->
           E. p e. ZZ
             (
               ( ( 2 ^ p ) - 1 ) e. Prime
               /\
               N = ( ( 2 ^ ( p - 1 ) ) x. ( ( 2 ^ p ) - 1 ) )
             )
         )
       )
  $.
$}
