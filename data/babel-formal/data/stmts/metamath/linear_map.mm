$(
  Statement-only formalization of the Babel-formal linear_map artifact:
  closure of linear-map kernels and images under vector addition and scalar
  multiplication. This file contains no proof.
$)

$(
  Statement-only encoding of a scalar field, two vector spaces over it,
  linear maps between those spaces, and closure of kernels and images under
  vector addition and scalar multiplication.

  Metamath variables in assertions and essential hypotheses are schematic.
  Every mathematical declaration and translated result is an unproved $a
  assertion; this database contains no $p proof statements.
$)

$c
  scalar vvec wvec lmap wff |-
  ( )
  zeroR oneR addR mulR oppR
  zeroV addV oppV smulV
  zeroW addW oppW smulW
  app
  =R =V =W
  /\ <->
  A.r A.v A.w E.v
  Field VSpaceV VSpaceW LinearMap Ker Im
$.

$v a b c x u v y z w L ph ps $.

sa $f scalar a $.
sb $f scalar b $.
sc $f scalar c $.

vx $f vvec x $.
vu $f vvec u $.
vv $f vvec v $.

wy $f wvec y $.
wz $f wvec z $.
ww $f wvec w $.

mL $f lmap L $.

wph $f wff ph $.
wps $f wff ps $.

zero-r-term $a scalar zeroR $.
one-r-term $a scalar oneR $.
add-r-term $a scalar ( addR a b ) $.
mul-r-term $a scalar ( mulR a b ) $.
opp-r-term $a scalar ( oppR a ) $.

zero-v-term $a vvec zeroV $.
add-v-term $a vvec ( addV x u ) $.
opp-v-term $a vvec ( oppV x ) $.
smul-v-term $a vvec ( smulV a x ) $.

zero-w-term $a wvec zeroW $.
add-w-term $a wvec ( addW y z ) $.
opp-w-term $a wvec ( oppW y ) $.
smul-w-term $a wvec ( smulW a y ) $.

map-app-term $a wvec ( app L x ) $.

eq-r-formula $a wff ( a =R b ) $.
eq-v-formula $a wff ( x =V u ) $.
eq-w-formula $a wff ( y =W z ) $.
and-formula $a wff ( ph /\ ps ) $.
iff-formula $a wff ( ph <-> ps ) $.
forall-r-formula $a wff ( A.r a ph ) $.
forall-v-formula $a wff ( A.v x ph ) $.
forall-w-formula $a wff ( A.w y ph ) $.
exists-v-formula $a wff ( E.v x ph ) $.

field-formula $a wff Field $.
vspace-v-formula $a wff VSpaceV $.
vspace-w-formula $a wff VSpaceW $.
linear-map-formula $a wff ( LinearMap L ) $.
kernel-formula $a wff ( Ker L x ) $.
image-formula $a wff ( Im L y ) $.

$(
  The scalar structure has exactly the operations and laws called Field in
  the source statements.
$)
field-def $a |- (
  Field
  <->
  (
    ( A.r a ( A.r b
      ( ( addR a b ) =R ( addR b a ) )
    ) )
    /\
    (
      ( A.r a ( A.r b ( A.r c
        ( ( addR ( addR a b ) c )
          =R
          ( addR a ( addR b c ) ) )
      ) ) )
      /\
      (
        ( A.r a
          ( ( addR a zeroR ) =R a )
        )
        /\
        (
          ( A.r a
            ( ( addR a ( oppR a ) ) =R zeroR )
          )
          /\
          (
            ( A.r a ( A.r b
              ( ( mulR a b ) =R ( mulR b a ) )
            ) )
            /\
            (
              ( A.r a ( A.r b ( A.r c
                ( ( mulR ( mulR a b ) c )
                  =R
                  ( mulR a ( mulR b c ) ) )
              ) ) )
              /\
              (
                ( A.r a
                  ( ( mulR a oneR ) =R a )
                )
                /\
                ( A.r a ( A.r b ( A.r c
                  ( ( mulR a ( addR b c ) )
                    =R
                    ( addR ( mulR a b ) ( mulR a c ) ) )
                ) ) )
              )
            )
          )
        )
      )
    )
  )
) $.

$(
  Source-vector-space structure over the scalar operations.
$)
vspace-v-def $a |- (
  VSpaceV
  <->
  (
    ( A.v x ( A.v u
      ( ( addV x u ) =V ( addV u x ) )
    ) )
    /\
    (
      ( A.v x ( A.v u ( A.v v
        ( ( addV ( addV x u ) v )
          =V
          ( addV x ( addV u v ) ) )
      ) ) )
      /\
      (
        ( A.v x
          ( ( addV x zeroV ) =V x )
        )
        /\
        (
          ( A.v x
            ( ( addV x ( oppV x ) ) =V zeroV )
          )
          /\
          (
            ( A.r a ( A.v x ( A.v u
              ( ( smulV a ( addV x u ) )
                =V
                ( addV ( smulV a x ) ( smulV a u ) ) )
            ) ) )
            /\
            (
              ( A.r a ( A.r b ( A.v x
                ( ( smulV ( addR a b ) x )
                  =V
                  ( addV ( smulV a x ) ( smulV b x ) ) )
              ) ) )
              /\
              (
                ( A.r a ( A.r b ( A.v x
                  ( ( smulV ( mulR a b ) x )
                    =V
                    ( smulV a ( smulV b x ) ) )
                ) ) )
                /\
                (
                  ( A.v x
                    ( ( smulV oneR x ) =V x )
                  )
                  /\
                  ( A.r a
                    ( ( smulV a zeroV ) =V zeroV )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
) $.

$(
  Target-vector-space structure over the same scalar operations.
$)
vspace-w-def $a |- (
  VSpaceW
  <->
  (
    ( A.w y ( A.w z
      ( ( addW y z ) =W ( addW z y ) )
    ) )
    /\
    (
      ( A.w y ( A.w z ( A.w w
        ( ( addW ( addW y z ) w )
          =W
          ( addW y ( addW z w ) ) )
      ) ) )
      /\
      (
        ( A.w y
          ( ( addW y zeroW ) =W y )
        )
        /\
        (
          ( A.w y
            ( ( addW y ( oppW y ) ) =W zeroW )
          )
          /\
          (
            ( A.r a ( A.w y ( A.w z
              ( ( smulW a ( addW y z ) )
                =W
                ( addW ( smulW a y ) ( smulW a z ) ) )
            ) ) )
            /\
            (
              ( A.r a ( A.r b ( A.w y
                ( ( smulW ( addR a b ) y )
                  =W
                  ( addW ( smulW a y ) ( smulW b y ) ) )
              ) ) )
              /\
              (
                ( A.r a ( A.r b ( A.w y
                  ( ( smulW ( mulR a b ) y )
                    =W
                    ( smulW a ( smulW b y ) ) )
                ) ) )
                /\
                (
                  ( A.w y
                    ( ( smulW oneR y ) =W y )
                  )
                  /\
                  ( A.r a
                    ( ( smulW a zeroW ) =W zeroW )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
) $.

$(
  A linear map preserves vector addition and scalar multiplication.
$)
linear-map-def $a |- (
  ( LinearMap L )
  <->
  (
    ( A.v x ( A.v u
      ( ( app L ( addV x u ) )
        =W
        ( addW ( app L x ) ( app L u ) ) )
    ) )
    /\
    ( A.r a ( A.v x
      ( ( app L ( smulV a x ) )
        =W
        ( smulW a ( app L x ) ) )
    ) )
  )
) $.

kernel-def $a |- (
  ( Ker L x )
  <->
  ( ( app L x ) =W zeroW )
) $.

image-def $a |- (
  ( Im L y )
  <->
  ( E.v x
    ( ( app L x ) =W y )
  )
) $.

$(
  The translated theorem family: the kernel and image of a linear map are
  closed under addition and scalar multiplication.
$)
${
  theorem-field-hyp $e |- Field $.
  theorem-vspace-v-hyp $e |- VSpaceV $.
  theorem-vspace-w-hyp $e |- VSpaceW $.
  theorem-linear-map-hyp $e |- ( LinearMap L ) $.

  ${
    ker-add-x-hyp $e |- ( Ker L x ) $.
    ker-add-u-hyp $e |- ( Ker L u ) $.

    ker-add $a |- ( Ker L ( addV x u ) ) $.
  $}

  ${
    ker-smul-x-hyp $e |- ( Ker L x ) $.

    ker-smul $a |- ( Ker L ( smulV a x ) ) $.
  $}

  ${
    im-add-y-hyp $e |- ( Im L y ) $.
    im-add-z-hyp $e |- ( Im L z ) $.

    im-add $a |- ( Im L ( addW y z ) ) $.
  $}

  ${
    im-smul-y-hyp $e |- ( Im L y ) $.

    im-smul $a |- ( Im L ( smulW a y ) ) $.
  $}
$}
