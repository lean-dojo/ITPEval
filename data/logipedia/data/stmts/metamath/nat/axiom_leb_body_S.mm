$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_leb_body_S (logipedia__metamath__nat.axiom_leb_body_S),
  catalog title "nat.axiom_leb_body_S": for every natural number n, the
  less-than-or-equal Boolean body at successor n equals the natural-number
  match function that returns false at zero and leb n q at successor q.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLeb and LogLebBody represent the fixed source constants of type

    NN0 -> NN0 -> {0,1}.

  LogMatchNatBool is nat.match_nat_type specialized to the Boolean carrier,
  with source type

    {0,1} -> (NN0 -> {0,1}) -> NN0 -> {0,1}.

  The nested maps-to terms preserve the source lambdas over m and q, and
  n + 1 is the natural-number successor S n. Native SetMM equality is
  bidirectionally equivalent to connectives.equal here: equal_leibniz yields
  native equality, while native equality rewrites the right side to the left
  and refl_equal supplies source reflexivity. The three preliminary $a
  declarations provide only class syntax for the fixed constants; the final
  $a is exactly the universally quantified source equation. This database
  contains no $p proof declaration.
$)

$c LogLeb LogLebBody LogMatchNatBool $.

log-leb-syntax $a class ( LogLeb ) $.
log-leb-body-syntax $a class ( LogLebBody ) $.
log-match-nat-bool-syntax $a class ( LogMatchNatBool ) $.

${
  $d m n q $.

  logipedia-nat-axiom-leb-body-s $a |-
    A. n e. NN0
      (
        ( LogLebBody ` ( n + 1 ) ) =
          (
            m e. NN0 |->
              (
                (
                  ( LogMatchNatBool ` 0 )
                  `
                  (
                    q e. NN0 |->
                      ( ( LogLeb ` n ) ` q )
                  )
                )
                `
                m
              )
          )
      )
  $.
$}
