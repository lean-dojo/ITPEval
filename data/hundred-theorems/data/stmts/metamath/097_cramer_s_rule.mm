$(
  Statement-only formalization of Hundred Theorems item 097, Cramer's rule
  over a commutative ring.

  This reproduces set.mm theorem cramer. The determinant of X is required to
  be a unit, and Z is the componentwise determinant quotient exactly when it
  solves XZ = Y.
$)

$[ library/set.mm $]

${
  $d B i $.
  $d D i $.
  $d i N $.
  $d R i $.
  $d i V $.
  $d i X $.
  $d i Y $.
  $d i Z $.
  $d .x. i $.
  $d ./ i $.

  hundred-theorems-097-matrix-algebra $e
    |- A = ( N Mat R )
  $.
  hundred-theorems-097-matrix-carrier $e
    |- B = ( Base ` A )
  $.
  hundred-theorems-097-vector-carrier $e
    |- V = ( ( Base ` R ) ^m N )
  $.
  hundred-theorems-097-determinant $e
    |- D = ( N maDet R )
  $.
  hundred-theorems-097-matrix-vector-product $e
    |- .x. = ( R maVecMul <. N , N >. )
  $.
  hundred-theorems-097-division $e
    |- ./ = ( /r ` R )
  $.

  hundred-theorems-097-cramer $a
    |- (
         (
           ( R e. CRing /\ N =/= (/) )
           /\
           ( X e. B /\ Y e. V )
           /\
           ( D ` X ) e. ( Unit ` R )
         )
         ->
         (
           Z =
             (
               i e. N |->
               (
                 ( D ` ( ( X ( N matRepV R ) Y ) ` i ) )
                 ./
                 ( D ` X )
               )
             )
           <->
           ( X .x. Z ) = Y
         )
       )
  $.
$}
