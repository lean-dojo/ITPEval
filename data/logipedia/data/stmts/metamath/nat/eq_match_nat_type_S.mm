$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_match_nat_type_S
  (logipedia__metamath__nat.eq_match_nat_type_S), catalog title
  "nat.eq_match_nat_type_S": for every result type, zero branch,
  successor branch, and natural number, natural-number elimination at the
  successor is Leibniz equal to the successor branch applied to that number.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source return type is represented by the SetMM carrier h,
  and the source natural-number type by NN0. The class ( h ^m NN0 ) is
  exactly the space of total functions from natural numbers to h.
  LogMatchNatType h represents nat.match_nat_type specialized to h, with
  the full curried source type

    h -> (NN0 -> h) -> NN0 -> h.

  SetMM's n + 1 is the source successor nat.S n. A predicate on h is
  represented extensionally by a subset p of h. Thus universal transport of
  membership from elimination at the successor to f at n is exactly the
  source definition of leibniz.leibniz in its stated direction. The typing
  conjunct and restricted universal quantifiers preserve the source
  declarations and all polymorphic binders. The final $a declaration is
  Metamath's native unproved statement encoding; this artifact introduces no
  $p proof declaration.
$)

$c LogMatchNatType $.

log-match-nat-type-syntax $a class ( LogMatchNatType h ) $.

${
  $d f h n p x $.

  logipedia-nat-eq-match-nat-type-s $a |-
    A. h
      (
        ( LogMatchNatType h ) e.
          ( ( ( h ^m NN0 ) ^m ( h ^m NN0 ) ) ^m h )
        /\
        A. x e. h
          A. f e. ( h ^m NN0 )
            A. n e. NN0
              A. p e. ~P h
                (
                  (
                    ( ( ( LogMatchNatType h ) ` x ) ` f ) ` ( n + 1 )
                  ) e. p
                  ->
                  ( ( f ` n ) e. p )
                )
      )
  $.
$}
