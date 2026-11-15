$(
  Statement-only formalization of the Babel-formal topic ideals. This file contains no proof.
$)

$(
  Statement-only encoding of commutative rings, ideals, intersections of
  indexed families of ideals, and sums of two ideals.
$)

$c evar ivar elt index pred family binop unop wff
   |- ( ) = /\ -> <-> A. E. A_i.
   app2 app1 holds At Inter IdealSum IsIdeal CRing $.

$v zero one x y z a b add mul opp I J F i u v j ph ps $.

vzero $f elt zero $.
vone  $f elt one $.
bx    $f evar x $.
by    $f evar y $.
bz    $f evar z $.
ba    $f evar a $.
bb    $f evar b $.
vadd  $f binop add $.
vmul  $f binop mul $.
vopp  $f unop opp $.
vI    $f pred I $.
vJ    $f pred J $.
vF    $f family F $.
bi    $f ivar i $.
vu    $f elt u $.
vv    $f elt v $.
vj    $f index j $.
wph   $f wff ph $.
wps   $f wff ps $.

evar-term $a elt x $.
ivar-term $a index i $.
tbin    $a elt ( app2 add u v ) $.
tun     $a elt ( app1 opp u ) $.
pat     $a pred ( At F j ) $.
pinter $a pred ( Inter F ) $.
psum    $a pred ( IdealSum add I J ) $.

weq    $a wff ( u = v ) $.
wholds $a wff ( holds I u ) $.
wand   $a wff ( ph /\ ps ) $.
wimp   $a wff ( ph -> ps ) $.
wiff   $a wff ( ph <-> ps ) $.
wall   $a wff ( A. x ph ) $.
wex    $a wff ( E. x ph ) $.
walli  $a wff ( A_i. i ph ) $.
wideal $a wff ( IsIdeal zero add mul opp I ) $.
wcring $a wff ( CRing zero one add mul opp ) $.

${
  $d x y z a $.
  $d x zero $.
  $d y zero $.
  $d z zero $.
  $d a zero $.
  $d x one $.
  $d y one $.
  $d z one $.
  $d a one $.
cringdef $a |- (
  ( CRing zero one add mul opp ) <->
  (
    ( A. x ( A. y
      ( ( app2 add x y ) = ( app2 add y x ) )
    ) )
    /\
    (
      ( A. x ( A. y ( A. z
        ( ( app2 add ( app2 add x y ) z )
          = ( app2 add x ( app2 add y z ) ) )
      ) ) )
      /\
      (
        ( A. x
          ( ( app2 add x zero ) = x )
        )
        /\
        (
          ( A. x
            ( ( app2 add x ( app1 opp x ) ) = zero )
          )
          /\
          (
            ( A. x ( A. y
              ( ( app2 mul x y ) = ( app2 mul y x ) )
            ) )
            /\
            (
              ( A. x ( A. y ( A. z
                ( ( app2 mul ( app2 mul x y ) z )
                  = ( app2 mul x ( app2 mul y z ) ) )
              ) ) )
              /\
              (
                ( A. x
                  ( ( app2 mul x one ) = x )
                )
                /\
                (
                  ( A. a ( A. x ( A. y
                    ( ( app2 mul a ( app2 add x y ) )
                      = ( app2 add
                          ( app2 mul a x )
                          ( app2 mul a y ) ) )
                  ) ) )
                  /\
                  ( A. x ( A. y
                    ( ( app1 opp ( app2 add x y ) )
                      = ( app2 add
                          ( app1 opp x )
                          ( app1 opp y ) ) )
                  ) )
                )
              )
            )
          )
        )
      )
    )
  )
) $.
$}

${
  $d x y a $.
  $d x zero $.
  $d y zero $.
  $d a zero $.
idealdef $a |- (
  ( IsIdeal zero add mul opp I ) <->
  (
    ( holds I zero )
    /\
    (
      ( A. x ( A. y
        ( ( holds I x ) ->
          ( ( holds I y ) ->
            ( holds I ( app2 add x y ) ) ) )
      ) )
      /\
      (
        ( A. x
          ( ( holds I x ) ->
            ( holds I ( app1 opp x ) ) )
        )
        /\
        ( A. a ( A. x
          ( ( holds I x ) ->
            ( holds I ( app2 mul a x ) ) )
        ) )
      )
    )
  )
) $.
$}

${
  $d x i $.
interdef $a |- (
  A. x
  (
    ( holds ( Inter F ) x ) <->
    ( A_i. i ( holds ( At F i ) x ) )
  )
) $.
$}

${
  $d x a b $.
sumdef $a |- (
  A. x
  (
    ( holds ( IdealSum add I J ) x ) <->
    ( E. a ( E. b
      (
        ( holds I a )
        /\
        (
          ( holds J b )
          /\
          ( x = ( app2 add a b ) )
        )
      )
    ) )
  )
) $.
$}

${
  hcring $e |- ( CRing zero one add mul opp ) $.

  ${
    hfamily $e |- (
      A_i. i
      ( IsIdeal zero add mul opp ( At F i ) )
    ) $.

    interisideal $a |- (
      IsIdeal zero add mul opp ( Inter F )
    ) $.
  $}

  ${
    hidealI $e |- ( IsIdeal zero add mul opp I ) $.
    hidealJ $e |- ( IsIdeal zero add mul opp J ) $.

    sumisideal $a |- (
      IsIdeal zero add mul opp ( IdealSum add I J )
    ) $.
  $}
$}
