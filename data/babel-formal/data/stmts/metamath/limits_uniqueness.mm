$(
  Statement-only formalization of the Babel-formal topic limits_uniqueness. This file contains
  no proof.
$)

$(
  Statement-only encoding of uniqueness of limits in the abstract structure
  used by the Lean and Rocq sources.

  ovar and ivar are binder-only variable sorts; obj and idx are the value and
  index term sorts, respectively, and seq is the sort of functions idx -> obj.
  The active essential hypotheses are exactly the primitive structure laws,
  the definition of subtraction, and the two limit assumptions.
  limit-unique is an unproved $a assertion; this database has no proofs.
$)

$c ovar ivar obj idx seq wff |- ( ) @ = -> A.o A.i E.i
   zero one add mul opp abs sub le lt nle nmax $.

$v xo yo zo ao bo co do eo ni nj nn nN x y l m i j u ph ps $.

bxo $f ovar xo $.
byo $f ovar yo $.
bzo $f ovar zo $.
bao $f ovar ao $.
bbo $f ovar bo $.
bco $f ovar co $.
bdo $f ovar do $.
beo $f ovar eo $.

bni $f ivar ni $.
bnj $f ivar nj $.
bnn $f ivar nn $.
bnN $f ivar nN $.

vx $f obj x $.
vy $f obj y $.
vl $f obj l $.
vm $f obj m $.

vi $f idx i $.
vj $f idx j $.

vu $f seq u $.

vph $f wff ph $.
vps $f wff ps $.

obj-var-term $a obj xo $.
idx-var-term $a idx ni $.
zero-term $a obj zero $.
one-term  $a obj one $.
add-term  $a obj ( add x y ) $.
mul-term  $a obj ( mul x y ) $.
opp-term  $a obj ( opp x ) $.
abs-term  $a obj ( abs x ) $.
sub-term  $a obj ( sub x y ) $.
apply-term $a obj ( u @ i ) $.
max-term  $a idx ( nmax i j ) $.

equality-formula $a wff ( x = y ) $.
le-formula       $a wff ( le x y ) $.
lt-formula       $a wff ( lt x y ) $.
nle-formula      $a wff ( nle i j ) $.
implication-formula $a wff ( ph -> ps ) $.
forall-obj-formula $a wff ( A.o xo ph ) $.
forall-idx-formula $a wff ( A.i ni ph ) $.
exists-idx-formula $a wff ( E.i ni ph ) $.

$d ni nj $.
$d xo yo $.
$d xo zo $.
$d yo zo $.
$d ao bo $.
$d ao co $.
$d ao do $.
$d bo co $.
$d bo do $.
$d co do $.
$d xo eo $.

${
  max-left $e |- ( A.i ni ( A.i nj
    ( nle ni ( nmax ni nj ) ) ) ) $.

  max-right $e |- ( A.i ni ( A.i nj
    ( nle nj ( nmax ni nj ) ) ) ) $.

  add-comm $e |- ( A.o xo ( A.o yo
    ( ( add xo yo ) = ( add yo xo ) ) ) ) $.

  add-assoc $e |- ( A.o xo ( A.o yo ( A.o zo
    ( ( add ( add xo yo ) zo ) = ( add xo ( add yo zo ) ) ) ) ) ) $.

  add-zero $e |- ( A.o xo
    ( ( add xo zero ) = xo ) ) $.

  add-opp $e |- ( A.o xo
    ( ( add xo ( opp xo ) ) = zero ) ) $.

  opp-add $e |- ( A.o xo ( A.o yo
    ( ( opp ( add xo yo ) ) = ( add ( opp xo ) ( opp yo ) ) ) ) ) $.

  mul-comm $e |- ( A.o xo ( A.o yo
    ( ( mul xo yo ) = ( mul yo xo ) ) ) ) $.

  mul-assoc $e |- ( A.o xo ( A.o yo ( A.o zo
    ( ( mul ( mul xo yo ) zo ) = ( mul xo ( mul yo zo ) ) ) ) ) ) $.

  mul-one $e |- ( A.o xo
    ( ( mul xo one ) = xo ) ) $.

  le-refl $e |- ( A.o xo
    ( le xo xo ) ) $.

  le-trans $e |- ( A.o xo ( A.o yo ( A.o zo
    ( ( le xo yo ) -> ( ( le yo zo ) -> ( le xo zo ) ) ) ) ) ) $.

  add-le-add $e |- ( A.o ao ( A.o bo ( A.o co ( A.o do
    ( ( le ao bo ) ->
      ( ( le co do ) ->
        ( le ( add ao co ) ( add bo do ) ) ) ) ) ) ) ) $.

  abs-nonneg $e |- ( A.o xo
    ( le zero ( abs xo ) ) ) $.

  abs-triangle $e |- ( A.o xo ( A.o yo
    ( le ( abs ( add xo yo ) ) ( add ( abs xo ) ( abs yo ) ) ) ) ) $.

  abs-opp $e |- ( A.o xo
    ( ( abs ( opp xo ) ) = ( abs xo ) ) ) $.

  abs-sub-symm $e |- ( A.o xo ( A.o yo
    ( ( abs ( add xo ( opp yo ) ) )
      =
      ( abs ( add yo ( opp xo ) ) ) ) ) ) $.

  sub-decomp $e |- ( A.o xo ( A.o yo ( A.o zo
    ( ( add xo ( opp zo ) )
      =
      ( add ( add xo ( opp yo ) ) ( add yo ( opp zo ) ) ) ) ) ) ) $.

  sub-eq-zero $e |- ( A.o xo ( A.o yo
    ( ( ( add xo ( opp yo ) ) = zero ) ->
      ( xo = yo ) ) ) ) $.

  eps-separation $e |- ( A.o xo
    ( ( A.o eo
        ( ( lt zero eo ) ->
          ( le ( abs xo ) ( add eo eo ) ) ) )
      ->
      ( xo = zero ) ) ) $.

  sub-definition $e |- ( A.o xo ( A.o yo
    ( ( sub xo yo ) = ( add xo ( opp yo ) ) ) ) ) $.

  abs-sub-triangle $a |- ( A.o xo ( A.o yo ( A.o zo
    ( le ( abs ( sub xo zo ) )
      ( add ( abs ( sub xo yo ) ) ( abs ( sub yo zo ) ) ) ) ) ) ) $.

  ${
    $d eo nN $.
    $d eo nn $.
    $d nN nn $.
    $d eo l $.
    $d eo m $.
    $d eo u $.
    $d nN l $.
    $d nN m $.
    $d nN u $.
    $d nn l $.
    $d nn m $.
    $d nn u $.

    limit-l $e |- ( A.o eo
      ( ( lt zero eo ) ->
        ( E.i nN ( A.i nn
          ( ( nle nN nn ) ->
            ( le ( abs ( sub ( u @ nn ) l ) ) eo ) ) ) ) ) ) $.

    limit-m $e |- ( A.o eo
      ( ( lt zero eo ) ->
        ( E.i nN ( A.i nn
          ( ( nle nN nn ) ->
            ( le ( abs ( sub ( u @ nn ) m ) ) eo ) ) ) ) ) ) $.

    limit-unique $a |- ( l = m ) $.
  $}
$}
