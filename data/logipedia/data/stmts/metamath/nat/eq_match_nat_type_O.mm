$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_match_nat_type_O
  (logipedia__metamath__nat.eq_match_nat_type_O), catalog title
  "nat.eq_match_nat_type_O": for every result type, zero branch, and
  successor branch, natural-number elimination at zero is Leibniz equal to
  the zero branch. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source return type is represented by the SetMM carrier h,
  and the source natural-number type by NN0. The class ( h ^m NN0 ) is
  exactly the space of total functions from natural numbers to h.
  LogMatchNatType h represents nat.match_nat_type specialized to h, with
  the full curried source type

    h -> (NN0 -> h) -> NN0 -> h.

  A predicate on h is represented extensionally by a subset p. Thus the
  bounded universal implication is exactly the source definition of
  leibniz.leibniz: every predicate holding of elimination at zero also holds
  of the zero branch. The typing conjunct and restricted universal
  quantifiers preserve the source declarations and all polymorphic binders.
  The final $a declaration is Metamath's native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c LogMatchNatType $.

log-match-nat-type-syntax $a class ( LogMatchNatType h ) $.

${
  $d f h p x $.

  logipedia-nat-eq-match-nat-type-o $a |-
    A. h
      (
        ( LogMatchNatType h ) e.
          ( ( ( h ^m NN0 ) ^m ( h ^m NN0 ) ) ^m h )
        /\
        A. x e. h
          A. f e. ( h ^m NN0 )
            A. p e. ~P h
              (
                ( ( ( ( LogMatchNatType h ) ` x ) ` f ) ` 0 ) e. p
                ->
                x e. p
              )
      )
  $.
$}
