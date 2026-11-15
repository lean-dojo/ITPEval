$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_plus (logipedia__metamath__nat.sym_eq_plus), catalog title
  "nat.sym_eq_plus": for every natural number, filter_nat_type applied to
  plus_body at that number is Leibniz equal to plus at the same number, as
  functions from naturals to naturals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 represents the source natural type. LogPlus is the curried natural
  addition function. LogPlusBody has the same extension: at zero it is the
  identity, and at successor n it maps m to the successor of LogPlus n m,
  exactly as in the source module. LogFilterNatTypeNat is filter_nat_type
  specialized to natural-valued unary-function results; because every NN0
  element is a natural constructor value, its source zero and successor
  equations make this specialization the identity on the full curried
  binary-function carrier.

  Predicates on the unary-function carrier are represented extensionally by
  its subsets p. Universal transport of membership from the filtered
  plus_body value to plus n is therefore exactly source Leibniz equality in
  the stated direction. The operation definitions provide the source
  signature typing context, so the root theorem has no added type-membership
  conjuncts. Every declaration is an unproved $a statement encoding; this
  file contains no $p proof declaration.
$)

$c LogPlus LogPlusBody LogFilterNatTypeNat $.

log-plus-syntax $a class ( LogPlus ) $.
log-plus-body-syntax $a class ( LogPlusBody ) $.
log-filter-nat-type-nat-syntax $a
  class ( LogFilterNatTypeNat )
$.

${
  $d f m n p $.

  log-plus-definition $a |-
    ( LogPlus ) =
      ( n e. NN0 |-> ( m e. NN0 |-> ( n + m ) ) )
  $.

  log-plus-body-definition $a |-
    ( LogPlusBody ) =
      ( n e. NN0 |-> ( m e. NN0 |-> ( n + m ) ) )
  $.

  log-filter-nat-type-nat-definition $a |-
    ( LogFilterNatTypeNat ) =
      (
        f e. ( ( NN0 ^m NN0 ) ^m NN0 ) |->
          f
      )
  $.

  logipedia-nat-sym-eq-plus $a |-
    A. n e. NN0
      A. p e. ~P ( NN0 ^m NN0 )
        (
          (
            (
              (
                ( LogFilterNatTypeNat )
                `
                ( LogPlusBody )
              )
              `
              n
            )
            e.
            p
          )
          ->
          ( ( ( LogPlus ) ` n ) e. p )
        )
  $.
$}
