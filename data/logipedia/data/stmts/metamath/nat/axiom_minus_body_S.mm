$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_minus_body_S
  (logipedia__metamath__nat.axiom_minus_body_S), catalog title
  "nat.axiom_minus_body_S": for every natural number n, the subtraction body
  at successor n equals the function obtained by natural-number matching,
  with successor n as the zero case and minus n q as the successor case.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogMinus and LogMinusBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogMatchNatNat represents nat.match_nat_type specialized to natural-number
  results, with source type

    NN0 -> (NN0 -> NN0) -> NN0 -> NN0.

  The nested maps-to terms preserve the source lambdas over m and q, and
  n + 1 is the natural-number successor S n.
  Native SetMM equality is bidirectionally equivalent to connectives.equal
  here: equal_leibniz yields native equality, while native equality rewrites
  the right side to the left and refl_equal supplies source reflexivity.
  The theorem states only the source equation; target-side typing facts are
  not added as extra conjuncts. All declarations are unproved $a statement
  encodings; this database contains no $p proof declaration.
$)

$c LogMinus LogMinusBody LogMatchNatNat $.

log-minus-syntax $a class ( LogMinus ) $.
log-minus-body-syntax $a class ( LogMinusBody ) $.
log-match-nat-nat-syntax $a class ( LogMatchNatNat ) $.

${
  $d m n q $.

  logipedia-nat-axiom-minus-body-s $a |-
    A. n e. NN0
      ( LogMinusBody ` ( n + 1 ) ) =
        (
          m e. NN0 |->
            (
              (
                ( LogMatchNatNat ` ( n + 1 ) )
                `
                (
                  q e. NN0 |->
                    ( ( LogMinus ` n ) ` q )
                )
              )
              `
              m
            )
        )
  $.
$}
