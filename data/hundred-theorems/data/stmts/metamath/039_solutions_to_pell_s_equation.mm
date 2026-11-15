$(
  Statement-only formalization of Hundred Theorems item 039, the complete
  classification of solutions to Pell's equation.

  The assertion is the proposition proved by set.mm theorem rmxycomplete.
  For A >= 2, rmX and rmY enumerate all integer solutions of
  X^2 - (A^2 - 1)Y^2 = 1. No proof is copied into this corpus file.
$)

$[ library/set.mm $]

${
  $d A n $.
  $d n X $.
  $d n Y $.

  hundred-theorems-039-pell-solutions $a
    |- (
         ( A e. ( ZZ>= ` 2 ) /\ X e. NN0 /\ Y e. ZZ )
         ->
         (
           ( ( X ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( Y ^ 2 ) ) ) = 1
           <->
           E. n e. ZZ
             ( X = ( A rmX n ) /\ Y = ( A rmY n ) )
         )
       )
  $.
$}
