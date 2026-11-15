$(
  Statement-only formalization of the Babel-formal topic graph_paths. This file contains no
  proof.
$)

$(
  Statement-only encoding of finite directed paths on an arbitrary vertex
  sort.  The relation sort represents Edge V.
$)

$c vertex relation wff |- ( ) -> /\ <-> A.v A.r Path Erev Undirected $.

$v E R u v w t x y z ph ps $.

rel-E $f relation E $.
rel-R $f relation R $.
vert-u $f vertex u $.
vert-v $f vertex v $.
vert-w $f vertex w $.
vert-t $f vertex t $.
vert-x $f vertex x $.
vert-y $f vertex y $.
vert-z $f vertex z $.
wff-ph $f wff ph $.
wff-ps $f wff ps $.

relation-application $a wff ( E u v ) $.
path-application $a wff ( Path E u v ) $.
reverse-relation $a relation ( Erev E ) $.
undirected-application $a wff ( Undirected E ) $.
implication $a wff ( ph -> ps ) $.
conjunction $a wff ( ph /\ ps ) $.
biconditional $a wff ( ph <-> ps ) $.
vertex-forall $a wff ( A.v x ph ) $.
relation-forall $a wff ( A.r R ph ) $.

$(
  Path E u v is the least binary relation that is reflexive and closed
  under extending a path by one E-edge on the right.
$)
path-definition $a |- (
  ( Path E u v ) <->
  ( A.r R (
    (
      ( A.v x ( R x x ) )
      /\
      ( A.v x ( A.v y ( A.v z (
        ( ( ( R x y ) /\ ( E y z ) ) -> ( R x z ) )
      ) ) ) )
    )
    -> ( R u v )
  ) )
) $.

erev-definition $a |- (
  ( ( Erev E ) x y ) <-> ( E y x )
) $.

undirected-definition $a |- (
  ( Undirected E ) <->
  ( A.v x ( A.v y ( ( E x y ) -> ( E y x ) ) ) )
) $.

path-nil $a |- ( Path E v v ) $.

${
  path-step.1 $e |- ( Path E u v ) $.
  path-step.2 $e |- ( E v w ) $.
  path-step $a |- ( Path E u w ) $.
$}

path-refl $a |- ( Path E v v ) $.

${
  append-right.1 $e |- ( Path E v w ) $.
  append-right.2 $e |- ( Path E u v ) $.
  append-right $a |- ( Path E u w ) $.
$}

${
  path-trans.1 $e |- ( Path E u v ) $.
  path-trans.2 $e |- ( Path E v w ) $.
  path-trans $a |- ( Path E u w ) $.
$}

${
  trans.1 $e |- ( Path E u v ) $.
  trans.2 $e |- ( Path E v w ) $.
  trans $a |- ( Path E u w ) $.
$}

${
  reverse-path.1 $e |- ( Undirected E ) $.
  reverse-path.2 $e |- ( Path E u v ) $.
  reverse-path $a |- ( Path E v u ) $.
$}

${
  concat-edge-right.1 $e |- ( Path E u v ) $.
  concat-edge-right.2 $e |- ( E v w ) $.
  concat-edge-right $a |- ( Path E u w ) $.
$}

${
  concat.1 $e |- ( Path E u v ) $.
  concat.2 $e |- ( Path E v w ) $.
  concat $a |- ( Path E u w ) $.
$}

${
  edge-path.1 $e |- ( E u v ) $.
  edge-path $a |- ( Path E u v ) $.
$}

${
  concat-edge-left.1 $e |- ( E u v ) $.
  concat-edge-left.2 $e |- ( Path E v w ) $.
  concat-edge-left $a |- ( Path E u w ) $.
$}

${
  concat3.1 $e |- ( Path E u v ) $.
  concat3.2 $e |- ( Path E v w ) $.
  concat3.3 $e |- ( Path E w t ) $.
  concat3 $a |- ( Path E u t ) $.
$}

${
  reverse-in-erev.1 $e |- ( Path E u v ) $.
  reverse-in-erev $a |- ( Path ( Erev E ) v u ) $.
$}

${
  cycle-refl.1 $e |- ( Path E v w ) $.
  cycle-refl.2 $e |- ( Path E w v ) $.
  cycle-refl $a |- ( Path E v v ) $.
$}
