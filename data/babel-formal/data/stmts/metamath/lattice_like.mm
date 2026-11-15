$(
  Statement-only formalization of the Babel-formal topic lattice_like. This file contains no
  proof.
$)

$(
  Statement-only encoding of a lattice-like structure on one abstract
  carrier.  LatticeLike packages a partial order together with binary meet
  and join operations satisfying their universal properties.  The six
  lattice laws are unproved $a assertions; this database has no $p
  statements.
$)

$c elt wff |- ( ) le inf sup = -> /\ <-> A. LatticeLike $.

$v a b c x y z ph ps $.

va  $f elt a $.
vb  $f elt b $.
vc  $f elt c $.
vx  $f elt x $.
vy  $f elt y $.
vz  $f elt z $.
wph $f wff ph $.
wps $f wff ps $.

tinf $a elt ( inf a b ) $.
tsup $a elt ( sup a b ) $.

wle      $a wff ( le a b ) $.
weq      $a wff ( a = b ) $.
wimp     $a wff ( ph -> ps ) $.
wand     $a wff ( ph /\ ps ) $.
wbi      $a wff ( ph <-> ps ) $.
wforall  $a wff ( A. x ph ) $.
wlattice $a wff LatticeLike $.

latticelikedef $a |- (
  LatticeLike <->
  (
    ( A. x ( le x x ) )
    /\
    (
      ( A. x ( A. y ( A. z
        ( ( ( le x y ) /\ ( le y z ) ) -> ( le x z ) )
      ) ) )
      /\
      (
        ( A. x ( A. y
          ( ( ( le x y ) /\ ( le y x ) ) -> ( x = y ) )
        ) )
        /\
        (
          ( A. a ( A. b ( le ( inf a b ) a ) ) )
          /\
          (
            ( A. a ( A. b ( le ( inf a b ) b ) ) )
            /\
            (
              ( A. c ( A. a ( A. b
                ( ( ( le c a ) /\ ( le c b ) )
                  -> ( le c ( inf a b ) ) )
              ) ) )
              /\
              (
                ( A. a ( A. b ( le a ( sup a b ) ) ) )
                /\
                (
                  ( A. a ( A. b ( le b ( sup a b ) ) ) )
                  /\
                  ( A. a ( A. b ( A. c
                    ( ( ( le a c ) /\ ( le b c ) )
                      -> ( le ( sup a b ) c ) )
                  ) ) )
                )
              )
            )
          )
        )
      )
    )
  )
) $.

${
  latticehyp $e |- LatticeLike $.

  infcomm $a |- (
    ( inf a b ) = ( inf b a )
  ) $.

  supcomm $a |- (
    ( sup a b ) = ( sup b a )
  ) $.

  infassoc $a |- (
    ( inf ( inf a b ) c ) = ( inf a ( inf b c ) )
  ) $.

  supassoc $a |- (
    ( sup ( sup a b ) c ) = ( sup a ( sup b c ) )
  ) $.

  infabsorption $a |- (
    ( inf a ( sup a b ) ) = a
  ) $.

  supabsorption $a |- (
    ( sup a ( inf a b ) ) = a
  ) $.
$}
