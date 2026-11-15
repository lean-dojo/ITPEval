$(
  Statement-only formalization of the Babel-formal galois artifact: field
  cancellation and inverses, and solvability of Galois groups along polynomial
  splitting-field towers. This file contains no proof.
$)

$(
  Statement-only translation of the Babel-formal galois artifact.

  The object language is many-sorted.  Field elements remain indexed by an
  explicit ambient type through In, while PolyOver and MapFrom retain the
  coefficient-field domains of polynomials and maps.  The endpoint-indexed
  term compose F K L g f is the source function x |-> g (f x).  Field and
  Tower are defined bidirectionally from the reified typing obligations and
  exactly the assumptions used by the source statements.  Every mathematical
  declaration below is an unproved $a assertion; this database has no proofs.
$)

$c type elem poly map group wff |- $.
$c ( ) -> <-> /\ -. A.t A.e A.p A.m $.
$c =e =p In PolyOver MapFrom FieldOps FieldLaws Field $.
$c TowerTyping TowerLaws Tower $.
$c zero one add mul opp inv $.
$c splitField alg apply compose mapPoly Gal IsSolvable Splits $.

$v F K L M $.
$v x y z $.
$v p q r s t $.
$v f g h $.
$v G $.
$v ph ps ch $.

vF $f type F $.
vK $f type K $.
vL $f type L $.
vM $f type M $.

vx $f elem x $.
vy $f elem y $.
vz $f elem z $.

vp $f poly p $.
vq $f poly q $.
vr $f poly r $.
vs $f poly s $.
vt $f poly t $.

vf $f map f $.
vg $f map g $.
vh $f map h $.

vG $f group G $.

wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

wi $a wff ( ph -> ps ) $.
wb $a wff ( ph <-> ps ) $.
wa $a wff ( ph /\ ps ) $.
wn $a wff ( -. ph ) $.

walt $a wff ( A.t F ph ) $.
wale $a wff ( A.e x ph ) $.
walp $a wff ( A.p p ph ) $.
walm $a wff ( A.m f ph ) $.

weqe $a wff ( x =e y ) $.
weqp $a wff ( p =p q ) $.
win $a wff ( In x F ) $.
wpoly $a wff ( PolyOver p F ) $.
wmap $a wff ( MapFrom f F K ) $.
wfieldops $a wff ( FieldOps F ) $.
wfieldlaws $a wff ( FieldLaws F ) $.
wfield $a wff ( Field F ) $.
wtowertyping $a wff TowerTyping $.
wtowerlaws $a wff TowerLaws $.
wtower $a wff Tower $.
wsolv $a wff ( IsSolvable G ) $.
wsplits $a wff ( Splits p f ) $.

tzero $a elem ( zero F ) $.
tone $a elem ( one F ) $.
tadd $a elem ( add F x y ) $.
tmul $a elem ( mul F x y ) $.
topp $a elem ( opp F x ) $.
tinv $a elem ( inv F x ) $.

tsplitfield $a type ( splitField p ) $.
talg $a map ( alg F K ) $.
tapply $a elem ( apply F K f x ) $.
tcompose $a map ( compose F K L g f ) $.
tmap $a poly ( mapPoly p f ) $.
tgal $a group ( Gal p ) $.

$(
  Field is definitionally equivalent to the source structure.  FieldOps
  reifies the closure facts supplied by the source types; FieldLaws is exactly
  the eleven proposition-valued fields of the Lean and Rocq classes.
$)

fieldopsdef $a |- ( ( FieldOps F ) <->
  ( ( In ( zero F ) F ) /\
    ( ( In ( one F ) F ) /\
      ( ( A.e x (
            ( In x F ) ->
            ( ( In ( opp F x ) F ) /\ ( In ( inv F x ) F ) )
          ) ) /\
        ( A.e x ( A.e y (
            ( ( In x F ) /\ ( In y F ) ) ->
            ( ( In ( add F x y ) F ) /\ ( In ( mul F x y ) F ) )
          ) ) ) ) ) )
) $.

fieldlawsdef $a |- ( ( FieldLaws F ) <->
  ( ( A.e x ( A.e y (
        ( ( In x F ) /\ ( In y F ) ) ->
        ( ( add F x y ) =e ( add F y x ) )
      ) ) ) /\
    ( ( A.e x ( A.e y ( A.e z (
          ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
          ( ( add F ( add F x y ) z ) =e
            ( add F x ( add F y z ) ) )
        ) ) ) ) /\
      ( ( A.e x (
            ( In x F ) -> ( ( add F x ( zero F ) ) =e x )
          ) ) /\
        ( ( A.e x (
              ( In x F ) ->
              ( ( add F ( opp F x ) x ) =e ( zero F ) )
            ) ) /\
          ( ( A.e x ( A.e y (
                ( ( In x F ) /\ ( In y F ) ) ->
                ( ( mul F x y ) =e ( mul F y x ) )
              ) ) ) /\
            ( ( A.e x ( A.e y ( A.e z (
                  ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
                  ( ( mul F ( mul F x y ) z ) =e
                    ( mul F x ( mul F y z ) ) )
                ) ) ) ) /\
              ( ( A.e x (
                    ( In x F ) -> ( ( mul F ( one F ) x ) =e x )
                  ) ) /\
                ( ( A.e x (
                      ( In x F ) ->
                      ( ( -. ( x =e ( zero F ) ) ) ->
                        ( ( mul F ( inv F x ) x ) =e ( one F ) ) )
                    ) ) /\
                  ( ( A.e x ( A.e y ( A.e z (
                        ( ( In x F ) /\
                          ( ( In y F ) /\ ( In z F ) ) ) ->
                        ( ( mul F x ( add F y z ) ) =e
                          ( add F
                            ( mul F x y )
                            ( mul F x z ) ) )
                      ) ) ) ) /\
                    ( ( -. ( ( zero F ) =e ( one F ) ) ) /\
                      ( A.e x (
                          ( In x F ) ->
                          ( ( -. ( x =e ( zero F ) ) ) ->
                            ( -. ( ( inv F x ) =e ( zero F ) ) ) )
                        ) ) ) ) ) ) ) ) ) ) ) ) )
) $.

fielddef $a |- ( ( Field F ) <->
  ( ( FieldOps F ) /\ ( FieldLaws F ) )
) $.

$(
  Tower is definitionally equivalent to the typed polynomial interface and
  the four polymorphic axioms in the source namespace.
$)

towertypingdef $a |- ( TowerTyping <->
  ( ( A.t F ( A.t K ( MapFrom ( alg F K ) F K ) ) ) /\
    ( ( A.t F ( A.t K (
          ( A.m f ( A.e x (
            ( ( MapFrom f F K ) /\ ( In x F ) ) ->
            ( In ( apply F K f x ) K )
          ) ) )
        ) ) ) /\
      ( ( A.t F ( A.t K ( A.t L (
            ( A.m f ( A.m g (
              ( ( MapFrom f F K ) /\ ( MapFrom g K L ) ) ->
              ( MapFrom ( compose F K L g f ) F L )
            ) ) )
          ) ) ) ) /\
        ( A.t F ( A.t K (
            ( A.p p ( A.m f (
              ( ( PolyOver p F ) /\ ( MapFrom f F K ) ) ->
              ( PolyOver ( mapPoly p f ) K )
            ) ) )
          ) ) ) ) ) )
) $.

$(
  This is the pointwise definition of the endpoint-indexed composition term.
  Its argument order follows the source lambda: compose F K L g f sends x to
  g (f x).
$)

composepointdef $a |- (
  A.t F ( A.t K ( A.t L (
    A.m f ( A.m g ( A.e x (
      ( ( MapFrom f F K ) /\
        ( ( MapFrom g K L ) /\ ( In x F ) ) ) ->
      ( ( apply F L ( compose F K L g f ) x ) =e
        ( apply K L g ( apply F K f x ) ) )
    ) ) )
  ) ) )
) $.

towerlawsdef $a |- ( TowerLaws <->
  ( ( A.t F ( A.t K ( A.t L (
        ( A.p p ( A.m f ( A.m g (
          ( ( PolyOver p F ) /\
            ( ( MapFrom f F K ) /\ ( MapFrom g K L ) ) ) ->
          ( ( mapPoly ( mapPoly p f ) g ) =p
            ( mapPoly p ( compose F K L g f ) ) )
        ) ) ) )
      ) ) ) ) /\
    ( ( A.t F ( A.t K (
          ( A.p p ( A.p q (
            ( ( PolyOver p F ) /\ ( PolyOver q F ) ) ->
            ( ( IsSolvable ( Gal p ) ) ->
              ( ( IsSolvable
                    ( Gal ( mapPoly q ( alg F K ) ) ) ) ->
                ( IsSolvable ( Gal q ) ) ) )
          ) ) )
        ) ) ) /\
      ( ( A.t F ( A.t K (
            ( A.p p (
              ( PolyOver p F ) ->
              ( ( IsSolvable ( Gal p ) ) ->
                ( IsSolvable
                  ( Gal ( mapPoly p ( alg F K ) ) ) )
            ) )
          ) ) ) /\
        ( A.t F ( A.t K (
            ( A.p p ( A.m f (
              ( ( PolyOver p F ) /\ ( MapFrom f F K ) ) ->
              ( ( Splits p f ) -> ( IsSolvable ( Gal p ) ) )
            ) ) )
          ) ) ) ) ) )
) $.

towerdef $a |- ( Tower <->
  ( TowerTyping /\ TowerLaws )
) $.

$(
  Field structure assumptions.
$)

fldaddcomm $a |- ( ( Field F ) ->
  ( A.e x ( A.e y (
    ( ( In x F ) /\ ( In y F ) ) ->
    ( ( add F x y ) =e ( add F y x ) )
  ) ) )
) $.

fldaddassoc $a |- ( ( Field F ) ->
  ( A.e x ( A.e y ( A.e z (
    ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
    ( ( add F ( add F x y ) z ) =e ( add F x ( add F y z ) ) )
  ) ) ) )
) $.

fldaddzero $a |- ( ( Field F ) ->
  ( A.e x (
    ( In x F ) ->
    ( ( add F x ( zero F ) ) =e x )
  ) )
) $.

fldaddinvl $a |- ( ( Field F ) ->
  ( A.e x (
    ( In x F ) ->
    ( ( add F ( opp F x ) x ) =e ( zero F ) )
  ) )
) $.

fldmulcomm $a |- ( ( Field F ) ->
  ( A.e x ( A.e y (
    ( ( In x F ) /\ ( In y F ) ) ->
    ( ( mul F x y ) =e ( mul F y x ) )
  ) ) )
) $.

fldmulassoc $a |- ( ( Field F ) ->
  ( A.e x ( A.e y ( A.e z (
    ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
    ( ( mul F ( mul F x y ) z ) =e ( mul F x ( mul F y z ) ) )
  ) ) ) )
) $.

fldmulonel $a |- ( ( Field F ) ->
  ( A.e x (
    ( In x F ) ->
    ( ( mul F ( one F ) x ) =e x )
  ) )
) $.

fldmulinvl $a |- ( ( Field F ) ->
  ( A.e x (
    ( In x F ) ->
    ( ( -. ( x =e ( zero F ) ) ) ->
      ( ( mul F ( inv F x ) x ) =e ( one F ) ) )
  ) )
) $.

flddistribl $a |- ( ( Field F ) ->
  ( A.e x ( A.e y ( A.e z (
    ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
    ( ( mul F x ( add F y z ) ) =e
      ( add F ( mul F x y ) ( mul F x z ) ) )
  ) ) ) )
) $.

fldzeroneqone $a |- ( ( Field F ) ->
  ( -. ( ( zero F ) =e ( one F ) ) )
) $.

fldinvnonzero $a |- ( ( Field F ) ->
  ( A.e x (
    ( In x F ) ->
    ( ( -. ( x =e ( zero F ) ) ) ->
      ( -. ( ( inv F x ) =e ( zero F ) ) ) )
  ) )
) $.

$(
  Field-property statements.
$)

addcancell $a |- ( ( Field F ) ->
  ( A.e x ( A.e y ( A.e z (
    ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
    ( ( ( add F x y ) =e ( add F x z ) ) -> ( y =e z ) )
  ) ) ) )
) $.

addcancelr $a |- ( ( Field F ) ->
  ( A.e x ( A.e y ( A.e z (
    ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
    ( ( ( add F y x ) =e ( add F z x ) ) -> ( y =e z ) )
  ) ) ) )
) $.

mulcancell $a |- ( ( Field F ) ->
  ( A.e x ( A.e y ( A.e z (
    ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
    ( ( -. ( x =e ( zero F ) ) ) ->
      ( ( ( mul F x y ) =e ( mul F x z ) ) -> ( y =e z ) ) )
  ) ) ) )
) $.

mulcancelr $a |- ( ( Field F ) ->
  ( A.e x ( A.e y ( A.e z (
    ( ( In x F ) /\ ( ( In y F ) /\ ( In z F ) ) ) ->
    ( ( -. ( x =e ( zero F ) ) ) ->
      ( ( ( mul F y x ) =e ( mul F z x ) ) -> ( y =e z ) ) )
  ) ) ) )
) $.

invunique $a |- ( ( Field F ) ->
  ( A.e x ( A.e y (
    ( ( In x F ) /\ ( In y F ) ) ->
    ( ( -. ( x =e ( zero F ) ) ) ->
      ( ( ( mul F x y ) =e ( one F ) ) ->
        ( y =e ( inv F x ) ) ) )
  ) ) )
) $.

invinvolutive $a |- ( ( Field F ) ->
  ( A.e x (
    ( In x F ) ->
    ( ( -. ( x =e ( zero F ) ) ) ->
      ( ( inv F ( inv F x ) ) =e x ) )
  ) )
) $.

$(
  Tower assumptions.  splitField p denotes the coefficient type of a
  splitting field for p, alg F K denotes the chosen algebra map F -> K, and
  compose F K L g f denotes the map F -> L taking x to g (f x).
$)

towermapcomp $a |- ( Tower ->
  ( A.t F ( A.t K ( A.t L (
    ( A.p p ( A.m f ( A.m g (
      ( ( PolyOver p F ) /\
        ( ( MapFrom f F K ) /\ ( MapFrom g K L ) ) ) ->
      ( ( mapPoly ( mapPoly p f ) g ) =p
        ( mapPoly p ( compose F K L g f ) ) )
    ) ) ) )
  ) ) ) )
) $.

towerscalar $a |- ( Tower ->
  ( A.t F ( A.t K (
    ( A.p p ( A.p q (
      ( ( PolyOver p F ) /\ ( PolyOver q F ) ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( ( IsSolvable ( Gal ( mapPoly q ( alg F K ) ) ) ) ->
          ( IsSolvable ( Gal q ) ) ) )
    ) ) )
  ) ) )
) $.

towermap $a |- ( Tower ->
  ( A.t F ( A.t K (
    ( A.p p (
      ( PolyOver p F ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( IsSolvable ( Gal ( mapPoly p ( alg F K ) ) ) )
    ) )
  ) ) )
) $.

towersplits $a |- ( Tower ->
  ( A.t F ( A.t K (
    ( A.p p ( A.m f (
      ( ( PolyOver p F ) /\ ( MapFrom f F K ) ) ->
      ( ( Splits p f ) -> ( IsSolvable ( Gal p ) ) )
    ) ) )
  ) ) )
) $.

$(
  Galois-solvability tower statements.
$)

galtower $a |- ( Tower ->
  ( A.t F (
    ( A.p p ( A.p q (
      ( ( PolyOver p F ) /\ ( PolyOver q F ) ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( ( IsSolvable
              ( Gal ( mapPoly q ( alg F ( splitField p ) ) ) ) ) ->
          ( IsSolvable ( Gal q ) ) ) )
    ) ) )
  ) )
) $.

galdoubletower $a |- ( Tower ->
  ( A.t F (
    ( A.p p ( A.p q ( A.p r (
      ( ( PolyOver p F ) /\
        ( ( PolyOver q F ) /\ ( PolyOver r F ) ) ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( ( IsSolvable
              ( Gal ( mapPoly q ( alg F ( splitField p ) ) ) ) ) ->
          ( ( IsSolvable
                ( Gal ( mapPoly r ( alg F ( splitField q ) ) ) ) ) ->
            ( IsSolvable ( Gal r ) ) ) ) )
    ) ) ) )
  ) )
) $.

galtripletower $a |- ( Tower ->
  ( A.t F (
    ( A.p p ( A.p q ( A.p r ( A.p s (
      ( ( PolyOver p F ) /\
        ( ( PolyOver q F ) /\
          ( ( PolyOver r F ) /\ ( PolyOver s F ) ) ) ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( ( IsSolvable
              ( Gal ( mapPoly q ( alg F ( splitField p ) ) ) ) ) ->
          ( ( IsSolvable
                ( Gal ( mapPoly r ( alg F ( splitField q ) ) ) ) ) ->
            ( ( IsSolvable
                  ( Gal ( mapPoly s ( alg F ( splitField r ) ) ) ) ) ->
              ( IsSolvable ( Gal s ) ) ) ) ) )
    ) ) ) ) )
  ) )
) $.

galquadtower $a |- ( Tower ->
  ( A.t F (
    ( A.p p ( A.p q ( A.p r ( A.p s ( A.p t (
      ( ( PolyOver p F ) /\
        ( ( PolyOver q F ) /\
          ( ( PolyOver r F ) /\
            ( ( PolyOver s F ) /\ ( PolyOver t F ) ) ) ) ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( ( IsSolvable
              ( Gal ( mapPoly q ( alg F ( splitField p ) ) ) ) ) ->
          ( ( IsSolvable
                ( Gal ( mapPoly r ( alg F ( splitField q ) ) ) ) ) ->
            ( ( IsSolvable
                  ( Gal ( mapPoly s ( alg F ( splitField r ) ) ) ) ) ->
              ( ( IsSolvable
                    ( Gal ( mapPoly t ( alg F ( splitField s ) ) ) ) ) ->
                ( IsSolvable ( Gal t ) ) ) ) ) ) )
    ) ) ) ) ) )
  ) )
) $.

galmap $a |- ( Tower ->
  ( A.t F ( A.t K (
    ( A.p p (
      ( PolyOver p F ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( IsSolvable ( Gal ( mapPoly p ( alg F K ) ) ) )
    ) )
  ) ) )
) $.

galofsplit $a |- ( Tower ->
  ( A.t F (
    ( A.p p (
      ( PolyOver p F ) ->
      ( ( Splits p ( alg F ( splitField p ) ) ) ->
        ( IsSolvable ( Gal p ) ) )
    ) )
  ) )
) $.

galsplittower $a |- ( Tower ->
  ( A.t F (
    ( A.p p ( A.p q (
      ( ( PolyOver p F ) /\ ( PolyOver q F ) ) ->
      ( ( Splits q ( alg F ( splitField p ) ) ) ->
        ( IsSolvable ( Gal q ) ) )
    ) ) )
  ) )
) $.

galtwostepmap $a |- ( Tower ->
  ( A.t F ( A.t K ( A.t L (
    ( A.p p (
      ( PolyOver p F ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( IsSolvable
          ( Gal
            ( mapPoly
              ( mapPoly p ( alg F K ) )
              ( alg K L ) ) ) ) )
    ) )
  ) ) ) )
) $.

galthreestepmap $a |- ( Tower ->
  ( A.t F ( A.t K ( A.t L ( A.t M (
    ( A.p p (
      ( PolyOver p F ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( IsSolvable
          ( Gal
            ( mapPoly
              ( mapPoly
                ( mapPoly p ( alg F K ) )
                ( alg K L ) )
              ( alg L M ) ) ) ) )
    ) )
  ) ) ) ) )
) $.

galmapcomp $a |- ( Tower ->
  ( A.t F ( A.t K ( A.t L (
    ( A.p p (
      ( PolyOver p F ) ->
      ( ( IsSolvable ( Gal p ) ) ->
        ( IsSolvable
          ( Gal
            ( mapPoly
              ( mapPoly p ( alg F K ) )
              ( alg K L ) ) ) ) )
    ) )
  ) ) ) )
) $.

galmutualsplit $a |- ( Tower ->
  ( A.t F (
    ( A.p p ( A.p q (
      ( ( PolyOver p F ) /\ ( PolyOver q F ) ) ->
      ( ( Splits p ( alg F ( splitField q ) ) ) ->
        ( ( Splits q ( alg F ( splitField p ) ) ) ->
          ( ( IsSolvable ( Gal p ) ) /\
            ( IsSolvable ( Gal q ) ) ) ) )
    ) ) )
  ) )
) $.

galtowersplit $a |- ( Tower ->
  ( A.t F (
    ( A.p p ( A.p q ( A.p r (
      ( ( PolyOver p F ) /\
        ( ( PolyOver q F ) /\ ( PolyOver r F ) ) ) ->
      ( ( Splits q ( alg F ( splitField p ) ) ) ->
        ( ( IsSolvable
              ( Gal ( mapPoly r ( alg F ( splitField q ) ) ) ) ) ->
          ( IsSolvable ( Gal r ) ) ) )
    ) ) ) )
  ) )
) $.

galmapaftersplit $a |- ( Tower ->
  ( A.t F ( A.t K (
    ( A.p p (
      ( PolyOver p F ) ->
      ( ( Splits p ( alg F ( splitField p ) ) ) ->
        ( IsSolvable ( Gal ( mapPoly p ( alg F K ) ) ) )
    ) )
  ) ) )
) $.
