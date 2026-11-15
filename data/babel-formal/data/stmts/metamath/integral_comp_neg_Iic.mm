$(
  Statement-only formalization of the Babel-formal topic integral_comp_neg_Iic. This file
  contains no proof.
$)

$(
  Statement-only encoding of an abstract ordered field, an abstract integral,
  interval domains, preimages, and the resulting integral identities.

  obj is the fixed arbitrary carrier R, fun is R -> R, and pred is R -> Prop.
  The RField and Integral class laws are explicit essential hypotheses.  Every
  definition and translated result is an unproved axiomatic assertion.
$)

$c ovar fvar pvar obj fun pred wff |-
   ( ) @ lambda plambda
   A.o A.f A.p
   = -> <-> /\ \/ -. F.
   zero one add opp mul le lt abs sigma
   Iic Ioi Iio union inter preimage holds $.

$v x y z c d f g h D E P u v qfun qpred rpred ph ps ch $.

bx  $f ovar x $.
by  $f ovar y $.
bz  $f ovar z $.
bc  $f ovar c $.
bd  $f ovar d $.
bf  $f fvar f $.
bg  $f fvar g $.
bh  $f fvar h $.
bD  $f pvar D $.
bE  $f pvar E $.
bP  $f pvar P $.
vu  $f obj u $.
vv  $f obj v $.
vqfun $f fun qfun $.
vqpred $f pred qpred $.
vrpred $f pred rpred $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

toVar    $a obj x $.
tfVar    $a fun f $.
tpVar    $a pred D $.
tzero    $a obj zero $.
tone     $a obj one $.
tadd     $a obj ( add u v ) $.
topp     $a obj ( opp u ) $.
tmul     $a obj ( mul u v ) $.
tabs     $a obj ( abs u ) $.
tapp     $a obj ( qfun @ u ) $.
tlambda  $a fun ( lambda x u ) $.
tplambda $a pred ( plambda x ph ) $.
toppfun  $a fun opp $.
tsigma   $a obj ( sigma qpred qfun ) $.

tiic      $a pred ( Iic u ) $.
tioi      $a pred ( Ioi u ) $.
tiio      $a pred ( Iio u ) $.
tunion    $a pred ( union qpred rpred ) $.
tinter    $a pred ( inter qpred rpred ) $.
tpreimage $a pred ( preimage qfun qpred ) $.

weq     $a wff ( u = v ) $.
wle     $a wff ( le u v ) $.
wlt     $a wff ( lt u v ) $.
wholds  $a wff ( holds qpred u ) $.
wimp    $a wff ( ph -> ps ) $.
wbi     $a wff ( ph <-> ps ) $.
wand    $a wff ( ph /\ ps ) $.
wor     $a wff ( ph \/ ps ) $.
wn      $a wff ( -. ph ) $.
wfalse  $a wff F. $.
wallobj $a wff ( A.o x ph ) $.
wallfun $a wff ( A.f f ph ) $.
wallpred $a wff ( A.p D ph ) $.

$d x y z c d f g h D E P $.

lambdaBeta $a |- ( A.o x
  ( ( ( lambda x u ) @ x ) = u ) ) $.

predicateLambdaBeta $a |- ( A.o x
  ( ( holds ( plambda x ph ) x ) <-> ph ) ) $.

oppFunctionDef $a |- ( A.o x
  ( ( opp @ x ) = ( opp x ) ) ) $.

iicDef $a |- ( A.o c
  ( A.o x
    ( ( holds ( Iic c ) x ) <-> ( le x c ) ) ) ) $.

ioiDef $a |- ( A.o c
  ( A.o x
    ( ( holds ( Ioi c ) x ) <-> ( lt c x ) ) ) ) $.

iioDef $a |- ( A.o c
  ( A.o x
    ( ( holds ( Iio c ) x ) <-> ( lt x c ) ) ) ) $.

unionDef $a |- ( A.p D
  ( A.p E
    ( A.o x
      ( ( holds ( union D E ) x )
        <->
        ( ( holds D x ) \/ ( holds E x ) ) ) ) ) ) $.

interDef $a |- ( A.p D
  ( A.p E
    ( A.o x
      ( ( holds ( inter D E ) x )
        <->
        ( ( holds D x ) /\ ( holds E x ) ) ) ) ) ) $.

preimageDef $a |- ( A.f f
  ( A.p D
    ( A.o x
      ( ( holds ( preimage f D ) x )
        <->
        ( holds D ( f @ x ) ) ) ) ) ) $.

preimageUnion $a |- ( A.p D
  ( A.p E
    ( A.f f
      ( A.o x
        ( ( holds ( preimage f ( union D E ) ) x )
          <->
          ( ( holds ( preimage f D ) x )
            \/
            ( holds ( preimage f E ) x ) ) ) ) ) ) ) $.

preimageInter $a |- ( A.p D
  ( A.p E
    ( A.f f
      ( A.o x
        ( ( holds ( preimage f ( inter D E ) ) x )
          <->
          ( ( holds ( preimage f D ) x )
            /\
            ( holds ( preimage f E ) x ) ) ) ) ) ) ) $.

preimageComp $a |- ( A.p D
  ( A.f g
    ( A.f h
      ( A.o x
        ( ( holds ( preimage g ( preimage h D ) ) x )
          <->
          ( holds
            ( preimage ( lambda x ( h @ ( g @ x ) ) ) D )
            x ) ) ) ) ) ) $.

${
  rfAddComm $e |- ( A.o x
    ( A.o y
      ( ( add x y ) = ( add y x ) ) ) ) $.

  rfAddAssoc $e |- ( A.o x
    ( A.o y
      ( A.o z
        ( ( add ( add x y ) z )
          =
          ( add x ( add y z ) ) ) ) ) ) $.

  rfAddZero $e |- ( A.o x
    ( ( add x zero ) = x ) ) $.

  rfAddOpp $e |- ( A.o x
    ( ( add ( opp x ) x ) = zero ) ) $.

  rfAddRightCancel $e |- ( A.o x
    ( A.o y
      ( A.o z
        ( ( ( add x z ) = ( add y z ) )
          ->
          ( x = y ) ) ) ) ) $.

  rfMulComm $e |- ( A.o x
    ( A.o y
      ( ( mul x y ) = ( mul y x ) ) ) ) $.

  rfMulAssoc $e |- ( A.o x
    ( A.o y
      ( A.o z
        ( ( mul ( mul x y ) z )
          =
          ( mul x ( mul y z ) ) ) ) ) ) $.

  rfMulOne $e |- ( A.o x
    ( ( mul x one ) = x ) ) $.

  rfDistL $e |- ( A.o x
    ( A.o y
      ( A.o z
        ( ( mul x ( add y z ) )
          =
          ( add ( mul x y ) ( mul x z ) ) ) ) ) ) $.

  rfOppInvolutive $e |- ( A.o x
    ( ( opp ( opp x ) ) = x ) ) $.

  rfAddLeCompat $e |- ( A.o x
    ( A.o y
      ( A.o z
        ( ( le x y )
          ->
          ( le ( add x z ) ( add y z ) ) ) ) ) ) $.

  rfMulLeCompat $e |- ( A.o x
    ( A.o y
      ( A.o z
        ( ( le zero z )
          ->
          ( ( le x y )
            ->
            ( le ( mul x z ) ( mul y z ) ) ) ) ) ) ) $.

  rfZeroLeOne $e |- ( le zero one ) $.

  rfLeTotal $e |- ( A.o x
    ( A.o y
      ( ( le x y ) \/ ( le y x ) ) ) ) $.

  rfLeDec $e |- ( A.o x
    ( A.o y
      ( ( le x y ) \/ ( -. ( le x y ) ) ) ) ) $.

  rfLeOpp $e |- ( A.o x
    ( A.o y
      ( ( le x y )
        ->
        ( le ( opp y ) ( opp x ) ) ) ) ) $.

  rfLeAntisymm $e |- ( A.o x
    ( A.o y
      ( ( le x y )
        ->
        ( ( le y x )
          ->
          ( x = y ) ) ) ) ) $.

  rfLtOpp $e |- ( A.o x
    ( A.o y
      ( ( lt x y )
        ->
        ( lt ( opp y ) ( opp x ) ) ) ) ) $.

  rfLeRefl $e |- ( A.o x
    ( le x x ) ) $.

  rfLeTrans $e |- ( A.o x
    ( A.o y
      ( A.o z
        ( ( le x y )
          ->
          ( ( le y z )
            ->
            ( le x z ) ) ) ) ) ) $.

  rfLtDef $e |- ( A.o x
    ( A.o y
      ( ( lt x y )
        <->
        ( ( le x y ) /\ ( -. ( x = y ) ) ) ) ) ) $.

  rfAbsPos $e |- ( A.o x
    ( ( le zero x )
      ->
      ( ( abs x ) = x ) ) ) $.

  rfAbsNeg $e |- ( A.o x
    ( ( le x zero )
      ->
      ( ( abs x ) = ( opp x ) ) ) ) $.

  rfAbsNonneg $e |- ( A.o x
    ( le zero ( abs x ) ) ) $.

  rfAbsOpp $e |- ( A.o x
    ( ( abs ( opp x ) ) = ( abs x ) ) ) $.

  rfAbsTriangle $e |- ( A.o x
    ( A.o y
      ( le
        ( abs ( add x y ) )
        ( add ( abs x ) ( abs y ) ) ) ) ) $.

  ltIrrefl $a |- ( A.o x
    ( -. ( lt x x ) ) ) $.

  ltTransStrict $a |- ( A.o x
    ( A.o y
      ( A.o z
        ( ( lt x y )
          ->
          ( ( lt y z )
            ->
            ( lt x z ) ) ) ) ) ) $.

  preimageNegIoi $a |- ( A.o c
    ( A.o x
      ( ( holds ( preimage opp ( Ioi c ) ) x )
        <->
        ( lt x ( opp c ) ) ) ) ) $.

  preimageNegIic $a |- ( A.o c
    ( A.o x
      ( ( holds ( preimage opp ( Iic c ) ) x )
        <->
        ( holds ( Iic x ) ( opp c ) ) ) ) ) $.

  ${
    intSigmaMulConst $e |- ( A.p D
      ( A.f f
        ( A.o c
          ( ( sigma D
              ( lambda x ( mul c ( f @ x ) ) ) )
            =
            ( mul c ( sigma D f ) ) ) ) ) ) $.

    intSigmaCongr $e |- ( A.p D
      ( A.f f
        ( A.f g
          ( ( A.o x
              ( ( holds D x )
                ->
                ( ( f @ x ) = ( g @ x ) ) ) )
            ->
            ( ( sigma D f ) = ( sigma D g ) ) ) ) ) ) $.

    intSigmaZero $e |- ( A.p D
      ( ( sigma D ( lambda x zero ) ) = zero ) ) $.

    intSigmaAdd $e |- ( A.p D
      ( A.f f
        ( A.f g
          ( ( sigma D
              ( lambda x ( add ( f @ x ) ( g @ x ) ) ) )
            =
            ( add ( sigma D f ) ( sigma D g ) ) ) ) ) ) $.

    intSigmaUnionDisjoint $e |- ( A.p D
      ( A.p E
        ( A.f f
          ( ( A.o x
              ( ( holds D x )
                ->
                ( ( holds E x ) -> F. ) ) )
            ->
            ( ( sigma
                ( plambda x
                  ( ( holds D x ) \/ ( holds E x ) ) )
                f )
              =
              ( add ( sigma D f ) ( sigma E f ) ) ) ) ) ) ) $.

    intSigmaLe $e |- ( A.p D
      ( A.f f
        ( A.f g
          ( ( A.o x
              ( ( holds D x )
                ->
                ( le ( f @ x ) ( g @ x ) ) ) )
            ->
            ( le ( sigma D f ) ( sigma D g ) ) ) ) ) ) $.

    intSigmaDomCongr $e |- ( A.p D
      ( A.p E
        ( A.f f
          ( ( A.o x
              ( ( holds D x ) <-> ( holds E x ) ) )
            ->
            ( ( sigma D f ) = ( sigma E f ) ) ) ) ) ) $.

    integralNeg $a |- ( A.p D
      ( A.f f
        ( ( sigma D
            ( lambda x ( opp ( f @ x ) ) ) )
          =
          ( opp ( sigma D f ) ) ) ) ) $.

    integralSub $a |- ( A.p D
      ( A.f f
        ( A.f g
          ( ( sigma D
              ( lambda x
                ( add ( f @ x ) ( opp ( g @ x ) ) ) ) )
            =
            ( add
              ( sigma D f )
              ( opp ( sigma D g ) ) ) ) ) ) ) $.

    sigmaEmpty $a |- ( A.f f
      ( ( sigma ( plambda x F. ) f ) = zero ) ) $.

    sigmaBilinear $a |- ( A.p D
      ( A.f f
        ( A.f g
          ( A.o c
            ( A.o d
              ( ( sigma D
                  ( lambda x
                    ( add
                      ( mul c ( f @ x ) )
                      ( mul d ( g @ x ) ) ) ) )
                =
                ( add
                  ( mul c ( sigma D f ) )
                  ( mul d ( sigma D g ) ) ) ) ) ) ) ) ) $.

    sigmaLeMonotone $a |- ( A.p D
      ( A.f f
        ( A.f g
          ( ( A.o x
              ( ( holds D x )
                ->
                ( le ( f @ x ) ( g @ x ) ) ) )
            ->
            ( le ( sigma D f ) ( sigma D g ) ) ) ) ) ) $.

    sigmaNonneg $a |- ( A.p D
      ( A.f f
        ( ( A.o x
            ( ( holds D x )
              ->
              ( le zero ( f @ x ) ) ) )
          ->
          ( le zero ( sigma D f ) ) ) ) ) $.

    sigmaSplit $a |- ( A.p D
      ( A.p P
        ( A.f f
          ( ( A.o x
              ( ( holds D x )
                ->
                ( ( holds P x )
                  \/
                  ( -. ( holds P x ) ) ) ) )
            ->
            ( ( sigma D f )
              =
              ( add
                ( sigma
                  ( plambda x
                    ( ( holds D x ) /\ ( holds P x ) ) )
                  f )
                ( sigma
                  ( plambda x
                    ( ( holds D x )
                      /\
                      ( -. ( holds P x ) ) ) )
                  f ) ) ) ) ) ) ) $.

    sigmaPreimageNegIoi $a |- ( A.f f
      ( A.o c
        ( ( sigma ( preimage opp ( Ioi c ) ) f )
          =
          ( sigma ( Iio ( opp c ) ) f ) ) ) ) $.

    sigmaAbsBound $a |- ( A.p D
      ( A.f f
        ( le
          ( abs ( sigma D f ) )
          ( sigma D
            ( lambda x ( abs ( f @ x ) ) ) ) ) ) ) $.
  $}
$}
