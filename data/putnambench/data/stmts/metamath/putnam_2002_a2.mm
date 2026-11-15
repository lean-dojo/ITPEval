$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2002_a2: among any five points on the unit sphere in real
  three-space, some four lie in a common closed hemisphere. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P02A2R3 is real coordinate three-space, P02A2Zero is its zero vector,
  P02A2IP is its standard inner product, P02A2Sphere is the unit sphere,
  and P02A2Hemi V is the closed hemisphere whose inward normal is V.
  Thus P02A2IP P P = 1 is equivalent to the source metric-sphere
  equation dist P 0 = 1, and membership in P02A2Hemi V is exactly the
  source condition that the inner product of P and V is nonnegative.

  Since the hypothesis gives S finite cardinality five, SetMM's finite
  cardinality of S intersect P02A2Hemi V agrees with the sources'
  extended-cardinality comparison. The nonzero normal V remains
  internally existentially quantified. Every declaration is an unproved
  $a statement encoding; this database contains no $p proof statement.
$)

$c P02A2R3 P02A2Zero P02A2IP P02A2Sphere P02A2Hemi $.

p02a2-space-syntax $a class P02A2R3 $.
p02a2-zero-syntax $a class P02A2Zero $.
p02a2-inner-product-syntax $a class ( P02A2IP A B ) $.
p02a2-sphere-syntax $a class P02A2Sphere $.
p02a2-hemisphere-syntax $a class ( P02A2Hemi V ) $.

p02a2-space-definition $a |- P02A2R3 = ( RR ^m 3 ) $.

${
  p02a2-zero-definition $a |- P02A2Zero =
    ( j e. 3 |-> 0 )
  $.
$}

${
  $d A B j $.

  p02a2-inner-product-definition $a |- (
    P02A2IP A B
  ) = (
    sum_ j e. 3
      ( ( A ` j ) x. ( B ` j ) )
  ) $.
$}

${
  p02a2-sphere-definition $a |- P02A2Sphere = {
    P e. P02A2R3 |
      ( P02A2IP P P ) = 1
  } $.
$}

${
  $d P V $.

  p02a2-hemisphere-definition $a |- (
    P02A2Hemi V
  ) = {
    P e. P02A2R3 |
      0 <_ ( P02A2IP P V )
  } $.
$}

${
  $d S V $.

  putnambench-putnam-2002-a2 $a |- A. S
    (
      (
        S C_ P02A2Sphere
        /\
        ( # ` S ) = 5
      )
      ->
      E. V e. P02A2R3
        (
          V =/= P02A2Zero
          /\
          4 <_ ( # ` ( S i^i ( P02A2Hemi V ) ) )
        )
    )
  $.
$}
