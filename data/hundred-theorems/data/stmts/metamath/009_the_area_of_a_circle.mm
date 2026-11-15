$(
  Statement-only formalization of Hundred Theorems item 009, the area of a
  Euclidean circle.

  This is the proposition proved by set.mm theorem areacirc. The essential
  hypothesis defines S as the closed radius-R disc in the real plane; area is
  set.mm's Lebesgue area. No proof is copied into this corpus file.
$)

$[ library/set.mm $]

${
  $d x y R $.

  hundred-theorems-009-disc $e
    |- S = { <. x , y >. |
              ( ( x e. RR /\ y e. RR ) /\
                ( ( x ^ 2 ) + ( y ^ 2 ) ) <_ ( R ^ 2 ) ) }
  $.

  hundred-theorems-009-area-of-a-circle $a
    |- (
         ( R e. RR /\ 0 <_ R )
         ->
         ( area ` S ) = ( _pi x. ( R ^ 2 ) )
       )
  $.
$}
