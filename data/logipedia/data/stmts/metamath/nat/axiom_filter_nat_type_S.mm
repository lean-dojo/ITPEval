$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_filter_nat_type_S
  (logipedia__metamath__nat.axiom_filter_nat_type_S), catalog title
  "nat.axiom_filter_nat_type_S": for every result type, natural-indexed
  function, and natural number, the source equality predicate relates
  filtering that function at the successor to its value at that successor.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source return type is represented by the SetMM carrier h.
  The class ( h ^m NN0 ) is exactly the space of total functions from natural
  numbers to h. LogFilterNatType h represents nat.filter_nat_type specialized
  to h, with the full curried source type

    (NN0 -> h) -> NN0 -> h.

  SetMM's n + 1 is the source successor nat.S n. LogConnectivesEqual retains
  the source's opaque type-indexed equality predicate. The typing conjunct and
  restricted universal quantifiers preserve the source declarations and all
  polymorphic binders. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c LogFilterNatType LogConnectivesEqual $.

log-filter-nat-type-syntax $a class ( LogFilterNatType h ) $.
log-connectives-equal-syntax $a wff
  ( LogConnectivesEqual h x y )
$.

${
  $d f h n $.

  logipedia-nat-axiom-filter-nat-type-s $a |-
    A. h
      (
        ( LogFilterNatType h ) e.
          ( ( h ^m NN0 ) ^m ( h ^m NN0 ) )
        /\
        A. f e. ( h ^m NN0 )
          A. n e. NN0
            (
              LogConnectivesEqual
              h
              ( ( ( LogFilterNatType h ) ` f ) ` ( n + 1 ) )
              ( f ` ( n + 1 ) )
            )
      )
  $.
$}
