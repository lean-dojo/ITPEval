$(
  Statement-only formalization of the Babel-formal topic comp_commute. This file contains no
  proof.
$)

$(
  A statement-only encoding of polymorphic function composition, identity,
  and commuting endomorphisms.
$)

$c type func wff |- ( ) -> => : = comp id commute <-> $.

$v A B C D f g h f1 f2 g1 g2 ph ps $.

ta $f type A $.
tb $f type B $.
tc $f type C $.
td $f type D $.

vf $f func f $.
vg $f func g $.
vh $f func h $.
vf1 $f func f1 $.
vf2 $f func f2 $.
vg1 $f func g1 $.
vg2 $f func g2 $.

vph $f wff ph $.
vps $f wff ps $.

warr $a type ( A -> B ) $.
wtyped $a wff ( f : ( A -> B ) ) $.
wcomp $a func ( comp A B C g f ) $.
wid $a func ( id A ) $.
weq $a wff ( f = g ) $.
wcomm $a wff ( commute A f g ) $.
wimp $a wff ( ph => ps ) $.
wbi $a wff ( ph <-> ps ) $.

${
  assocf $e |- ( f : ( A -> B ) ) $.
  assocg $e |- ( g : ( B -> C ) ) $.
  assoch $e |- ( h : ( C -> D ) ) $.
  compassoc $a |- (
    ( comp A C D h ( comp A B C g f ) )
    =
    ( comp A B D ( comp B C D h g ) f )
  ) $.
$}

${
  identityf $e |- ( f : ( A -> B ) ) $.
  compidl $a |- (
    ( comp A B B ( id B ) f ) = f
  ) $.
  compidr $a |- (
    ( comp A A B f ( id A ) ) = f
  ) $.
$}

${
  deff $e |- ( f : ( A -> A ) ) $.
  defg $e |- ( g : ( A -> A ) ) $.
  commutedef $a |- (
    ( commute A f g )
    <->
    ( ( comp A A A f g ) = ( comp A A A g f ) )
  ) $.
$}

${
  symmf $e |- ( f : ( A -> A ) ) $.
  symmg $e |- ( g : ( A -> A ) ) $.
  commutesymm $a |- (
    ( commute A f g ) => ( commute A g f )
  ) $.
$}

${
  unitf $e |- ( f : ( A -> A ) ) $.
  commutewithidl $a |- ( commute A f ( id A ) ) $.
  commutewithidr $a |- ( commute A ( id A ) f ) $.
  commuterefl $a |- ( commute A f f ) $.
$}

${
  congrf1 $e |- ( f1 : ( A -> A ) ) $.
  congrf2 $e |- ( f2 : ( A -> A ) ) $.
  congrg1 $e |- ( g1 : ( A -> A ) ) $.
  congrg2 $e |- ( g2 : ( A -> A ) ) $.
  commutecongr $a |- (
    ( f1 = f2 ) =>
    ( ( g1 = g2 ) =>
      ( ( commute A f1 g1 ) => ( commute A f2 g2 ) )
    )
  ) $.
$}

${
  transportf $e |- ( f : ( A -> A ) ) $.
  transportg $e |- ( g : ( A -> A ) ) $.
  commutetransportleftid $a |- (
    ( commute A f g ) =>
    ( commute A ( comp A A A ( id A ) f ) g )
  ) $.
  commutetransportrightid $a |- (
    ( commute A f g ) =>
    ( commute A f ( comp A A A ( id A ) g ) )
  ) $.
$}
