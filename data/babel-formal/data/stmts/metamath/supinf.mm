$(
  Statement-only formalization of the Babel-formal topic supinf. This file contains no proof.
$)

$(
  Statement-only encoding of the abstract complete ordered field context,
  bounds, infima, limits, and the reciprocal-sequence bound from the Lean
  and Rocq sources.

  rvar, nvar, and svar are binder-only variable sorts.  rterm and nterm are
  the field and alternative-natural term sorts, rset is the sort of
  predicates on rterm, and seq is the sort of functions from nterm to rterm.
  The source's set-valued low_bounds operation is represented by the
  extensionally equivalent binary predicate lowBounds.  The source's unusual
  completeness law assumes only that the set has a lower bound, but concludes
  that it has a least upper bound.

  The primitive structure laws are active essential hypotheses.  All
  definitions and translated results are unproved $a assertions; this
  database contains no $p statements.
$)

$c
  rvar nvar svar rterm nterm rset seq wff |-
  ( ) @
  zero one add mul opp inv abs zeroN inr succ
  =R nle rle rlt member
  -> <-> /\ \/ -.
  A.R E.R A.N E.N A.S
  upBounds isMaximum lowBounds isInf limit
$.

$v
  x y z a b t eps ub s l r q
  n m N i j
  A B
  u v
  ph ps
$.

rx   $f rvar x $.
ry   $f rvar y $.
rz   $f rvar z $.
ra   $f rvar a $.
rb   $f rvar b $.
rt   $f rvar t $.
reps $f rvar eps $.
rub  $f rvar ub $.
rs   $f rvar s $.
rl   $f rvar l $.
rr   $f rterm r $.
rq   $f rterm q $.

nn $f nvar n $.
nm $f nvar m $.
nN $f nvar N $.
ni $f nterm i $.
nj $f nterm j $.

sA $f svar A $.
sB $f rset B $.

qu $f seq u $.
qv $f seq v $.

wph $f wff ph $.
wps $f wff ps $.

real-var-term $a rterm x $.
nat-var-term  $a nterm n $.
set-var-term  $a rset A $.
zero-term $a rterm zero $.
one-term  $a rterm one $.
add-term  $a rterm ( add r q ) $.
mul-term  $a rterm ( mul r q ) $.
opp-term  $a rterm ( opp r ) $.
inv-term  $a rterm ( inv r ) $.
abs-term  $a rterm ( abs r ) $.
inr-term  $a rterm ( inr i ) $.
zero-nat-term $a nterm zeroN $.
succ-term $a nterm ( succ i ) $.
apply-term $a rterm ( v @ i ) $.

eq-formula     $a wff ( r =R q ) $.
nle-formula    $a wff ( nle i j ) $.
rle-formula    $a wff ( rle r q ) $.
rlt-formula    $a wff ( rlt r q ) $.
member-formula $a wff ( member r B ) $.

imp-formula $a wff ( ph -> ps ) $.
iff-formula $a wff ( ph <-> ps ) $.
and-formula $a wff ( ph /\ ps ) $.
or-formula  $a wff ( ph \/ ps ) $.
not-formula $a wff ( -. ph ) $.

forall-r-formula $a wff ( A.R x ph ) $.
exists-r-formula $a wff ( E.R x ph ) $.
forall-n-formula $a wff ( A.N n ph ) $.
exists-n-formula $a wff ( E.N n ph ) $.
forall-set-formula $a wff ( A.S A ph ) $.

up-bounds-formula  $a wff ( upBounds B r ) $.
is-maximum-formula $a wff ( isMaximum r B ) $.
low-bounds-formula $a wff ( lowBounds B r ) $.
is-inf-formula     $a wff ( isInf r B ) $.
limit-formula      $a wff ( limit v r ) $.

${
  $d a r $.
  $d a B $.

  up-bounds-definition $a |- (
    ( upBounds B r )
    <->
    ( A.R a
      ( ( member a B ) -> ( rle a r ) ) )
  ) $.
$}

is-maximum-definition $a |- (
  ( isMaximum r B )
  <->
  ( ( member r B ) /\ ( upBounds B r ) )
) $.

${
  $d a r $.
  $d a B $.

  low-bounds-definition $a |- (
    ( lowBounds B r )
    <->
    ( A.R a
      ( ( member a B ) -> ( rle r a ) ) )
  ) $.
$}

${
  $d y r $.
  $d y B $.

  is-inf-definition $a |- (
    ( isInf r B )
    <->
    (
      ( lowBounds B r )
      /\
      ( A.R y
        ( ( lowBounds B y ) -> ( rle y r ) ) )
    )
  ) $.
$}

${
  $d eps r $.
  $d N n $.
  $d N r $.
  $d n r $.

  limit-definition $a |- (
    ( limit v r )
    <->
    ( A.R eps
      (
        ( rlt zero eps )
        ->
        ( E.N N
          ( A.N n
            (
              ( nle N n )
              ->
              ( rle
                ( abs ( add ( v @ n ) ( opp r ) ) )
                eps
              )
            )
          )
        )
      )
    )
  ) $.
$}

excluded-middle $a |- ( ph \/ ( -. ph ) ) $.

${
  $d x y z $.
  $d n m $.
  $d a b $.
  $d x eps $.
  $d y eps $.
  $d A ub a s y $.

  nat-refl $e |- (
    A.N n ( nle n n )
  ) $.

  nat-le-succ-of-le $e |- (
    A.N n
      ( A.N m
        ( ( nle n m ) -> ( nle n ( succ m ) ) )
      )
  ) $.

  nat-le-succ $e |- (
    A.N n ( nle n ( succ n ) )
  ) $.

  add-comm $e |- (
    A.R x
      ( A.R y
        ( ( add x y ) =R ( add y x ) )
      )
  ) $.

  add-assoc $e |- (
    A.R x
      ( A.R y
        ( A.R z
          (
            ( add ( add x y ) z )
            =R
            ( add x ( add y z ) )
          )
        )
      )
  ) $.

  add-zero $e |- (
    A.R x ( ( add x zero ) =R x )
  ) $.

  add-opp $e |- (
    A.R x ( ( add ( opp x ) x ) =R zero )
  ) $.

  mul-comm $e |- (
    A.R x
      ( A.R y
        ( ( mul x y ) =R ( mul y x ) )
      )
  ) $.

  mul-assoc $e |- (
    A.R x
      ( A.R y
        ( A.R z
          (
            ( mul ( mul x y ) z )
            =R
            ( mul x ( mul y z ) )
          )
        )
      )
  ) $.

  mul-one $e |- (
    A.R x ( ( mul x one ) =R x )
  ) $.

  dist-left $e |- (
    A.R x
      ( A.R y
        ( A.R z
          (
            ( mul x ( add y z ) )
            =R
            ( add ( mul x y ) ( mul x z ) )
          )
        )
      )
  ) $.

  sub-zero $e |- (
    A.R x ( ( add x ( opp zero ) ) =R x )
  ) $.

  rle-refl $e |- (
    A.R x ( rle x x )
  ) $.

  rle-trans $e |- (
    A.R x
      ( A.R y
        ( A.R z
          (
            ( rle x y )
            ->
            ( ( rle y z ) -> ( rle x z ) )
          )
        )
      )
  ) $.

  rle-antisym $e |- (
    A.R x
      ( A.R y
        (
          ( rle x y )
          ->
          ( ( rle y x ) -> ( x =R y ) )
        )
      )
  ) $.

  rlt-definition $e |- (
    A.R x
      ( A.R y
        (
          ( rlt x y )
          <->
          ( ( rle x y ) /\ ( -. ( x =R y ) ) )
        )
      )
  ) $.

  rle-abs $e |- (
    A.R x
      ( rle ( add x ( opp zero ) ) ( abs x ) )
  ) $.

  inv-positive $e |- (
    A.R x
      (
        ( rlt zero x )
        ->
        ( rlt zero ( inv x ) )
      )
  ) $.

  add-le-compat-left $e |- (
    A.R x
      ( A.R y
        ( A.R z
          (
            ( rle y z )
            ->
            ( rle ( add x y ) ( add x z ) )
          )
        )
      )
  ) $.

  inv-involutive-positive $e |- (
    A.R x
      (
        ( rlt zero x )
        ->
        ( ( inv ( inv x ) ) =R x )
      )
  ) $.

  inr-positive-succ $e |- (
    A.N n
      ( rlt zero ( inr ( succ n ) ) )
  ) $.

  inr-monotone $e |- (
    A.N m
      ( A.N n
        (
          ( nle m n )
          ->
          ( rle ( inr m ) ( inr n ) )
        )
      )
  ) $.

  inr-zero $e |- (
    ( inr zeroN ) =R zero
  ) $.

  inr-succ $e |- (
    A.N n
      (
        ( inr ( succ n ) )
        =R
        ( add ( inr n ) one )
      )
  ) $.

  rtotal-order $e |- (
    A.R x
      ( A.R y
        (
          ( rlt x y )
          \/
          ( ( x =R y ) \/ ( rlt y x ) )
        )
      )
  ) $.

  inv-order-reversing $e |- (
    A.R a
      ( A.R b
        (
          ( rlt zero a )
          ->
          (
            ( rlt zero b )
            ->
            (
              ( rle a b )
              ->
              ( rle ( inv b ) ( inv a ) )
            )
          )
        )
      )
  ) $.

  eps-between $e |- (
    A.R x
      ( A.R y
        (
          ( rlt x y )
          ->
          ( E.R eps
            (
              ( rlt zero eps )
              /\
              ( rlt ( add x eps ) y )
            )
          )
        )
      )
  ) $.

  archimedean $e |- (
    A.R x
      ( E.N n ( rle x ( inr n ) ) )
  ) $.

  completeness $e |- (
    A.S A
      (
        ( E.R ub
          ( A.R a
            ( ( member a A ) -> ( rle ub a ) )
          )
        )
        ->
        ( E.R s
          (
            ( A.R a
              ( ( member a A ) -> ( rle a s ) )
            )
            /\
            ( A.R y
              (
                ( A.R a
                  ( ( member a A ) -> ( rle a y ) )
                )
                ->
                ( rle s y )
              )
            )
          )
        )
      )
  ) $.

  add-sub-cancel-r $a |- (
    ( add r ( add q ( opp r ) ) ) =R q
  ) $.

  rabs-pos $a |- (
    rle r ( abs r )
  ) $.

  unique-max $a |- (
    ( isMaximum r B )
    ->
    ( ( isMaximum q B ) -> ( r =R q ) )
  ) $.

${
    $d y a $.
    $d y r $.
    $d a r $.
    $d y B $.
    $d a B $.

    inf-lt $a |- (
      ( isInf r B )
      ->
      ( A.R y
        (
          ( rlt r y )
          ->
          ( E.R a
            ( ( member a B ) /\ ( rlt a y ) )
          )
        )
      )
    ) $.
  $}

${
    $d eps r $.
    $d eps q $.

    le-of-le-add-eps $a |- (
      ( A.R eps
        (
          ( rlt zero eps )
          ->
          ( rle q ( add r eps ) )
        )
      )
      ->
      ( rle q r )
    ) $.
  $}

${
    $d n r $.
    $d n q $.

    le-lim $a |- (
      ( limit v r )
      ->
      (
        ( A.N n ( rle q ( v @ n ) ) )
        ->
        ( rle q r )
      )
    ) $.
  $}

  inv-succ-pos $a |- (
    rlt zero ( inv ( inr ( succ i ) ) )
  ) $.

${
    $d N n $.
    $d N r $.
    $d n r $.

    limit-inv-succ $a |- (
      ( rlt zero r )
      ->
      ( E.N N
        ( A.N n
          (
            ( nle N n )
            ->
            ( rle ( inv ( inr ( succ n ) ) ) r )
          )
        )
      )
    ) $.
  $}
$}
