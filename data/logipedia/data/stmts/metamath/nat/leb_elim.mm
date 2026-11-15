$(
  Statement-only formalization of the Logipedia corpus artifact nat.leb_elim
  (logipedia__metamath__nat.leb_elim), catalog title "nat.leb_elim":
  elimination for Boolean less-than-or-equal on natural numbers, where
  predicates at the true and false order cases determine the predicate at
  leb. This file contains no proof.
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
  hypotheses of the artifact and not a definition by the cases that this
  eliminator must establish. The source Boolean carrier is { 0 , 1 }, with
  true represented by 1 and false by 0. A predicate P : bool -> Prop is
  represented extensionally by a subset p of this carrier, so b e. p means
  P b. SetMM's native non-strict order on NN0 represents nat.le. The final $a
  declaration preserves the source binder order, assumptions, and conclusion;
  this artifact adds no $p proof declaration.
$)

$c LogLeb $.

log-leb-syntax $a class ( LogLeb ) $.

log-leb-type $a |-
  ( LogLeb ) e. ( ( { 0 , 1 } ^m NN0 ) ^m NN0 )
$.

${
  $d m n p $.

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

  logipedia-nat-leb-elim $a |-
    A. n e. NN0
      A. m e. NN0
        A. p e. ~P { 0 , 1 }
          (
            ( n <_ m -> 1 e. p )
            ->
            (
              ( -. n <_ m -> 0 e. p )
              ->
              ( ( LogLeb ` n ) ` m ) e. p
            )
          )
  $.
$}
