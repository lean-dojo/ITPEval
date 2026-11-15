$(
  Statement-only formalization of the Babel-formal topic group. This file contains no proof.
$)

$(
  Statement-only encoding of groups, commutative groups, group actions,
  orbits, and stabilizers.  The mathematical declarations and results are
  unproved $a assertions; this database contains no $p statements.
$)

$c
  gvar xvar gterm xterm wff |-
  ( )
  one inv mul act
  =G =X
  -> <-> /\
  A.G A.X E.G
  Group CommGroup Action orbit stabilizer
$.

$v a b c g h x y z u v r s ph ps $.

ba  $f gvar a $.
bb  $f gvar b $.
bc  $f gvar c $.
bg  $f gvar g $.
bh  $f gvar h $.
bx  $f xvar x $.
by  $f xvar y $.
bz  $f xvar z $.
gu  $f gterm u $.
gv  $f gterm v $.
xr  $f xterm r $.
xs  $f xterm s $.
wph $f wff ph $.
wps $f wff ps $.

wgvar $a gterm a $.
wxvar $a xterm x $.
wgone $a gterm one $.
wginv $a gterm ( inv u ) $.
wgmul $a gterm ( mul u v ) $.
wxact $a xterm ( act u r ) $.

weqg $a wff ( u =G v ) $.
weqx $a wff ( r =X s ) $.
wimp $a wff ( ph -> ps ) $.
wbi $a wff ( ph <-> ps ) $.
wand $a wff ( ph /\ ps ) $.
wforallg $a wff ( A.G a ph ) $.
wforallx $a wff ( A.X x ph ) $.
wexistsg $a wff ( E.G a ph ) $.

wisgroup $a wff Group $.
wiscommgroup $a wff CommGroup $.
wisaction $a wff Action $.
worbit $a wff ( orbit r s ) $.
wstabilizer $a wff ( stabilizer r u ) $.

${
  $d a b c $.
  groupdef $a |- ( Group <->
    (
      ( A.G a ( A.G b ( A.G c
        ( ( mul a ( mul b c ) ) =G ( mul ( mul a b ) c ) )
      ) ) )
      /\
      (
        ( A.G a ( ( mul a one ) =G a ) )
        /\
        (
          ( A.G a ( ( mul one a ) =G a ) )
          /\
          (
            ( A.G a ( ( mul ( inv a ) a ) =G one ) )
            /\
            ( A.G a ( ( mul a ( inv a ) ) =G one ) )
          )
        )
      )
    )
  ) $.
$}

${
  $d a b $.
  commgroupdef $a |- ( CommGroup <->
    (
      Group
      /\
      ( A.G a ( A.G b ( ( mul a b ) =G ( mul b a ) ) ) )
    )
  ) $.
$}

${
  $d g h x $.
  actiondef $a |- ( Action <->
    (
      Group
      /\
      (
        ( A.X x ( ( act one x ) =X x ) )
        /\
        ( A.G g ( A.G h ( A.X x
          ( ( act ( mul g h ) x ) =X ( act g ( act h x ) ) )
        ) ) )
      )
    )
  ) $.
$}

${
  grouphyp $e |- Group $.

  ${
    mulleftcancelhyp $e |- ( ( mul a b ) =G ( mul a c ) ) $.
    mulleftcancel $a |- ( b =G c ) $.
  $}

  ${
    mulrightcancelhyp $e |- ( ( mul b a ) =G ( mul c a ) ) $.
    mulrightcancel $a |- ( b =G c ) $.
  $}

  invinv $a |- ( ( inv ( inv a ) ) =G a ) $.

  invmul $a |- (
    ( inv ( mul a b ) ) =G ( mul ( inv b ) ( inv a ) )
  ) $.

  ${
    inveqofmuleqonehyp $e |- ( ( mul a b ) =G one ) $.
    inveqofmuleqone $a |- ( b =G ( inv a ) ) $.
  $}
$}

${
  commgrouphyp $e |- CommGroup $.

  mulrotate $a |- (
    ( mul a ( mul b c ) ) =G ( mul b ( mul c a ) )
  ) $.
$}

${
  actionhyp $e |- Action $.

  ${
    $d g x $.
    $d g y $.
    orbitdef $a |- (
      ( orbit x y ) <-> ( E.G g ( ( act g x ) =X y ) )
    ) $.
  $}

  stabilizerdef $a |- (
    ( stabilizer x g ) <-> ( ( act g x ) =X x )
  ) $.

  actinv $a |- ( ( act ( inv g ) ( act g x ) ) =X x ) $.

  actinvr $a |- ( ( act g ( act ( inv g ) x ) ) =X x ) $.

  orbitrefl $a |- ( orbit x x ) $.

  ${
    orbitsymhyp $e |- ( orbit x y ) $.
    orbitsym $a |- ( orbit y x ) $.
  $}

  ${
    orbittranshypone $e |- ( orbit x y ) $.
    orbittranshyptwo $e |- ( orbit y z ) $.
    orbittrans $a |- ( orbit x z ) $.
  $}

  ${
    orbitpartitionhyp $e |- ( orbit x y ) $.
    orbitpartition $a |- (
      ( orbit x z ) <-> ( orbit y z )
    ) $.
  $}

  ${
    stabilizermulhypone $e |- ( stabilizer x g ) $.
    stabilizermulhyptwo $e |- ( stabilizer x h ) $.
    stabilizermul $a |- ( stabilizer x ( mul g h ) ) $.
  $}

  ${
    stabilizerinvhyp $e |- ( stabilizer x g ) $.
    stabilizerinv $a |- ( stabilizer x ( inv g ) ) $.
  $}

  stabilizerone $a |- ( stabilizer x one ) $.

  ${
    stabilizerconjugatehyp $e |- ( stabilizer x h ) $.
    stabilizerconjugate $a |- (
      stabilizer ( act g x ) ( mul ( mul g h ) ( inv g ) )
    ) $.
  $}

  ${
    stabilizerconjugateorbithyp $e |- ( ( act g x ) =X y ) $.
    stabilizerconjugateorbit $a |- (
      ( stabilizer y h )
      <->
      ( stabilizer x ( mul ( mul ( inv g ) h ) g ) )
    ) $.
  $}
$}
