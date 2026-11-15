$(
  Statement-only formalization of Hundred Theorems item 010, Euler's
  generalization of Fermat's little theorem.

  The assertion is the proposition proved by set.mm theorem eulerth. N is a
  positive integer, A is an integer coprime to N, and phi is Euler's totient.
  No proof is copied into this corpus file.
$)

$[ library/set.mm $]

hundred-theorems-010-euler-totient $a
  |- (
       ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 )
       ->
       ( ( A ^ ( phi ` N ) ) mod N ) = ( 1 mod N )
     )
$.
