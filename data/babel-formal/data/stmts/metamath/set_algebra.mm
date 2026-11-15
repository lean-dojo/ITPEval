$(
  Statement-only formalization of the Babel-formal topic set_algebra. This file contains no
  proof.
$)

$(
  Statement-only encoding of Boolean algebra on predicates over one abstract
  carrier.  Predicate-valued functions are represented as sets, with their
  operations characterized pointwise.  All mathematical declarations and
  results are unproved $a assertions; this database has no $p statements.
$)

$c elt set wff |- ( ) e. sUnion sInter sCompl \/ /\ -. <-> A. $.

$v A B C x ph ps $.

vA  $f set A $.
vB  $f set B $.
vC  $f set C $.
vx  $f elt x $.
vph $f wff ph $.
vps $f wff ps $.

tsunion $a set ( sUnion A B ) $.
tsinter $a set ( sInter A B ) $.
tscompl $a set ( sCompl A ) $.

wmem    $a wff ( x e. A ) $.
wor     $a wff ( ph \/ ps ) $.
wand    $a wff ( ph /\ ps ) $.
wnot    $a wff ( -. ph ) $.
wbi     $a wff ( ph <-> ps ) $.
wforall $a wff ( A. x ph ) $.

classic $a |- ( ph \/ ( -. ph ) ) $.

suniondef $a |- (
  A. x (
    ( x e. ( sUnion A B ) )
    <->
    ( ( x e. A ) \/ ( x e. B ) )
  )
) $.

sinterdef $a |- (
  A. x (
    ( x e. ( sInter A B ) )
    <->
    ( ( x e. A ) /\ ( x e. B ) )
  )
) $.

scompldef $a |- (
  A. x (
    ( x e. ( sCompl A ) )
    <->
    ( -. ( x e. A ) )
  )
) $.

interdistribleft $a |- (
  A. x (
    ( x e. ( sInter A ( sUnion B C ) ) )
    <->
    ( x e. ( sUnion ( sInter A B ) ( sInter A C ) ) )
  )
) $.

interdistribright $a |- (
  A. x (
    ( x e. ( sInter ( sUnion A B ) C ) )
    <->
    ( x e. ( sUnion ( sInter A C ) ( sInter B C ) ) )
  )
) $.

demorganunion $a |- (
  A. x (
    ( x e. ( sCompl ( sUnion A B ) ) )
    <->
    ( x e. ( sInter ( sCompl A ) ( sCompl B ) ) )
  )
) $.

demorganinter $a |- (
  A. x (
    ( x e. ( sCompl ( sInter A B ) ) )
    <->
    ( x e. ( sUnion ( sCompl A ) ( sCompl B ) ) )
  )
) $.
