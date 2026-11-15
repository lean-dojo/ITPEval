$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_filter_nat_type_O
  (logipedia__metamath__nat.eq_filter_nat_type_O), catalog title
  "nat.eq_filter_nat_type_O": for every result type and natural-indexed
  function, filtering that function at zero is Leibniz equal to its value at
  zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source return type is represented by the SetMM carrier h.
  The class ( h ^m NN0 ) is exactly the space of total functions from natural
  numbers to h. LogFilterNatType h represents nat.filter_nat_type specialized
  to h, with the full curried source type

    (NN0 -> h) -> NN0 -> h.

  A predicate on h is represented extensionally by a subset p of h. Thus
  universal transport of membership from the filtered value at zero to f at
  zero is exactly the source definition of leibniz.leibniz in its stated
  direction. The typing conjunct and restricted universal quantifier preserve
  the source declarations and both polymorphic binders. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c LogFilterNatType $.

log-filter-nat-type-syntax $a class ( LogFilterNatType h ) $.

${
  $d f h p $.

  logipedia-nat-eq-filter-nat-type-o $a |-
    A. h
      (
        ( LogFilterNatType h ) e.
          ( ( h ^m NN0 ) ^m ( h ^m NN0 ) )
        /\
        A. f e. ( h ^m NN0 )
          A. p e. ~P h
            (
              ( ( ( ( LogFilterNatType h ) ` f ) ` 0 ) e. p )
              ->
              ( ( f ` 0 ) e. p )
            )
      )
  $.
$}
