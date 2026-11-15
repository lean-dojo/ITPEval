$(
  Statement-only formalization of Babel-formal artifact zero_le_one_elem:
  the identity/zero matrices and all nine indexed pointwise preorder and
  equality statements. This database contains no proof.
$)

$(
  Bound indices and elements have dedicated variable-only syntactic sorts.
  Distinct-variable conditions on the definitions prevent binder capture.
$)

$c
  ivar evar index elem matrix wff |-
  ( )
  -> /\ \/ <-> -. =e
  A.i A.e
  decEq ite le entry matrixLe matrixEq
  zero one ZeroM OneM
$.

$v
  iv jv ev fv gv
  i j x y z
  A B C
  ph ps
$.

biv $f ivar iv $.
bjv $f ivar jv $.
bev $f evar ev $.
bfv $f evar fv $.
bgv $f evar gv $.

ii $f index i $.
ij $f index j $.
ex $f elem x $.
ey $f elem y $.
ez $f elem z $.
mA $f matrix A $.
mB $f matrix B $.
mC $f matrix C $.
wph $f wff ph $.
wps $f wff ps $.

$d iv jv $.
$d ev fv gv $.

index-variable-term $a index iv $.
element-variable-term $a elem ev $.

zero-term $a elem zero $.
one-term $a elem one $.
zero-matrix-term $a matrix ZeroM $.
one-matrix-term $a matrix OneM $.

matrix-entry-term $a elem ( entry A i j ) $.
ite-term $a elem ( ite ph x y ) $.

dec-eq-formula $a wff ( decEq i j ) $.
le-formula $a wff ( le x y ) $.
element-equality $a wff ( x =e y ) $.
matrix-le-formula $a wff ( matrixLe A B ) $.
matrix-eq-formula $a wff ( matrixEq A B ) $.

implication $a wff ( ph -> ps ) $.
conjunction $a wff ( ph /\ ps ) $.
disjunction $a wff ( ph \/ ps ) $.
biconditional $a wff ( ph <-> ps ) $.
negation $a wff ( -. ph ) $.
forall-index $a wff ( A.i iv ph ) $.
forall-element $a wff ( A.e ev ph ) $.

${
  ite-definition $a |- (
    ( z =e ( ite ph x y ) )
    <->
    (
      ( ph /\ ( z =e x ) )
      \/
      ( ( -. ph ) /\ ( z =e y ) )
    )
  ) $.

  dec-eq-cases $a |- (
    ( decEq i j ) \/ ( -. ( decEq i j ) )
  ) $.
$}

${
  $d iv jv $.
  zero-matrix-definition $a |- (
    A.i iv
      ( A.i jv
        ( ( entry ZeroM iv jv ) =e zero ) )
  ) $.

  one-matrix-definition $a |- (
    A.i iv
      ( A.i jv
        (
          ( entry OneM iv jv )
          =e
          ( ite ( decEq iv jv ) one zero )
        )
      )
  ) $.
$}

${
  $d iv jv $.
  $d iv A $.
  $d iv B $.
  $d jv A $.
  $d jv B $.

  matrix-le-definition $a |- (
    ( matrixLe A B )
    <->
    ( A.i iv
      ( A.i jv
        ( le ( entry A iv jv ) ( entry B iv jv ) )
      )
    )
  ) $.

  matrix-eq-definition $a |- (
    ( matrixEq A B )
    <->
    ( A.i iv
      ( A.i jv
        ( ( entry A iv jv ) =e ( entry B iv jv ) )
      )
    )
  ) $.
$}

${
  preorder-refl $e |- (
    A.e ev ( le ev ev )
  ) $.

  preorder-trans $e |- (
    A.e ev
      ( A.e fv
        ( A.e gv
          (
            ( le ev fv )
            ->
            ( ( le fv gv ) -> ( le ev gv ) )
          )
        )
      )
  ) $.

  zero-le-one $e |- ( le zero one ) $.
  zero-le-zero $e |- ( le zero zero ) $.

  zero-le-one-elem $a |- (
    le zero ( entry OneM i j )
  ) $.

  zero-le-one-matrix $a |- (
    matrixLe ZeroM OneM
  ) $.

  matrix-le-refl $a |- (
    matrixLe A A
  ) $.

  ${
    matrix-le-trans-left $e |- ( matrixLe A B ) $.
    matrix-le-trans-right $e |- ( matrixLe B C ) $.
    matrix-le-trans $a |- ( matrixLe A C ) $.
  $}

  matrix-eq-refl $a |- (
    matrixEq A A
  ) $.

  ${
    matrix-eq-sym-hyp $e |- ( matrixEq A B ) $.
    matrix-eq-sym $a |- ( matrixEq B A ) $.
  $}

  ${
    matrix-eq-trans-left $e |- ( matrixEq A B ) $.
    matrix-eq-trans-right $e |- ( matrixEq B C ) $.
    matrix-eq-trans $a |- ( matrixEq A C ) $.
  $}

  ${
    matrix-eq-le-hyp $e |- ( matrixEq A B ) $.
    matrix-eq-le $a |- (
      ( matrixLe A B ) /\ ( matrixLe B A )
    ) $.
  $}

  ${
    partial-order-antisym $e |- (
      A.e ev
        ( A.e fv
          (
            ( le ev fv )
            ->
            ( ( le fv ev ) -> ( ev =e fv ) )
          )
        )
    ) $.

    matrix-le-antisymm-left $e |- ( matrixLe A B ) $.
    matrix-le-antisymm-right $e |- ( matrixLe B A ) $.
    matrix-le-antisymm $a |- ( matrixEq A B ) $.
  $}
$}
