$(
  Statement-only formalization of Hundred Theorems item 071, Lagrange's
  theorem for finite groups.

  This is the proposition proved by set.mm theorem lagsubg. X is the carrier
  of G and Y is a subgroup of G.
$)

$[ library/set.mm $]

${
  hundred-theorems-071-group-carrier $e
    |- X = ( Base ` G )
  $.

  hundred-theorems-071-lagrange $a
    |- (
         ( Y e. ( SubGrp ` G ) /\ X e. Fin )
         ->
         ( # ` Y ) || ( # ` X )
       )
  $.
$}
