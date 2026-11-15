$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_eqb_body_S (logipedia__metamath__nat.sym_eq_eqb_body_S),
  catalog title "nat.sym_eq_eqb_body_S": for every natural number n, the
  natural-number match function returning false at zero and eqb n q at
  successor q is Leibniz equal, as a function from natural numbers to
  Booleans, to eqb_body at successor n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's natural-number carrier, and {0,1} is the Boolean carrier,
  with false represented by 0 and true by 1. The definitions below render
  nat.eqb and nat.eqb_body as the Boolean characteristic function of equality.
  They render nat.match_nat_type on Booleans by selecting the zero branch at
  zero and applying the successor branch to the predecessor otherwise.

  For any set p, membership in p is a predicate; conversely, every predicate
  on the source function type is represented extensionally by its set of
  satisfying functions. Thus the final assertion is exactly the source
  Leibniz-equality universal transport

    forall p, p matcher_function -> p (eqb_body (S n)),

  with no typing facts conjoined to the conclusion. The definitions and final
  $a declaration are unproved statement encodings; this file has no $p proof
  declaration.
$)

$c LogEqb LogEqbBody LogMatchNatBool $.

log-eqb-syntax $a class ( LogEqb ) $.
log-eqb-body-syntax $a class ( LogEqbBody ) $.
log-match-nat-bool-syntax $a class ( LogMatchNatBool ) $.

${
  $d f m n p q x $.

  log-eqb-definition $a |-
    ( LogEqb ) =
      (
        n e. NN0 |->
          (
            q e. NN0 |->
              if ( n = q , 1 , 0 )
          )
      )
  $.

  log-eqb-body-definition $a |-
    ( LogEqbBody ) =
      (
        n e. NN0 |->
          (
            m e. NN0 |->
              if ( n = m , 1 , 0 )
          )
      )
  $.

  log-match-nat-bool-definition $a |-
    ( LogMatchNatBool ) =
      (
        x e. { 0 , 1 } |->
          (
            f e. ( { 0 , 1 } ^m NN0 ) |->
              (
                m e. NN0 |->
                  if ( m = 0 , x , ( f ` ( m - 1 ) ) )
              )
          )
      )
  $.

  logipedia-nat-sym-eq-eqb-body-s $a |-
    A. n e. NN0
      A. p
        (
          (
            (
              m e. NN0 |->
                (
                  (
                    ( LogMatchNatBool ` 0 )
                    `
                    (
                      q e. NN0 |->
                        ( ( LogEqb ` n ) ` q )
                    )
                  )
                  `
                  m
                )
            )
            e.
            p
          )
          ->
          ( ( LogEqbBody ` ( n + 1 ) ) e. p )
        )
  $.
$}
