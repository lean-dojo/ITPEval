$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_leb_true (logipedia__metamath__nat.le_to_leb_true), catalog title
  "nat.le_to_leb_true": if one natural number is less than or equal to
  another, their Boolean less-than-or-equal test returns true. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. LogLeb represents the fixed source constant nat.leb
  with curried type NN0 -> NN0 -> {0,1}. Its three declarations below encode
  the source computation independently of order:

    leb 0 m = true,
    leb (S n) 0 = false,
    leb (S n) (S m) = leb n m.

  These declarations are the exact recursive source context, not added
  hypotheses of the artifact and not a definition in terms of the theorem's
  conclusion. SetMM's native non-strict order represents nat.le, true is 1,
  and native equality represents source equality on Boolean values in this
  embedding. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

$c LogLeb $.

log-leb-syntax $a class ( LogLeb ) $.

log-leb-type $a |-
  ( LogLeb ) e. ( ( { 0 , 1 } ^m NN0 ) ^m NN0 )
$.

${
  $d m n $.

  log-leb-zero $a |-
    A. m e. NN0
      ( ( ( LogLeb ` 0 ) ` m ) = 1 )
  $.

  log-leb-succ-zero $a |-
    A. n e. NN0
      ( ( ( LogLeb ` ( n + 1 ) ) ` 0 ) = 0 )
  $.

  log-leb-succ-succ $a |-
    A. n e. NN0 A. m e. NN0
      (
        ( ( LogLeb ` ( n + 1 ) ) ` ( m + 1 ) )
        =
        ( ( LogLeb ` n ) ` m )
      )
  $.

  logipedia-nat-le-to-leb-true $a |-
    A. n e. NN0
      A. m e. NN0
        (
          n <_ m
          ->
          ( ( LogLeb ` n ) ` m ) = 1
        )
  $.
$}
