$(
  Statement-only formalization of Hundred Theorems item 096, the principle
  of inclusion-exclusion for a finite family of finite sets.

  This is the proposition proved by set.mm theorem incexc.
$)

$[ library/set.mm $]

${
  $d A s $.

  hundred-theorems-096-inclusion-exclusion $a
    |- (
         ( A e. Fin /\ A C_ Fin )
         ->
         ( # ` U. A )
         =
         sum_ s e. ( ~P A \ { (/) } )
           (
             ( -u 1 ^ ( ( # ` s ) - 1 ) )
             x.
             ( # ` |^| s )
           )
       )
  $.
$}
