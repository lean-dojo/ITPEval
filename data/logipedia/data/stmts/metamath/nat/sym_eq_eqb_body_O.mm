$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_eqb_body_O (logipedia__metamath__nat.sym_eq_eqb_body_O),
  catalog title "nat.sym_eq_eqb_body_O": the natural-number match function
  returning true at zero and false at every successor is Leibniz equal, as a
  function from natural numbers to Booleans, to the equality-test body at
  zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's natural-number carrier, and {0,1} is the Boolean carrier,
  with true represented by 1 and false by 0. Hence

    ( m e. NN0 |-> if ( m = 0 , 1 , 0 ) )

  is the direct target-native rendering of

    fun m => match_nat_type bool true (fun q => false) m.

  LogEqbBody represents the fixed source constant nat.eqb_body, so
  ( LogEqbBody ` 0 ) renders eqb_body O. For any set p, membership in p is a
  predicate; conversely, every predicate on the source function type is
  extensionally represented by its set of satisfying functions. Quantifying
  over every set p therefore unfolds the source Leibniz predicate without
  adding typing conjuncts or restricting it to a fixed predicate carrier.
  The final $a declaration is an unproved statement encoding; this artifact
  introduces no $p proof declaration.
$)

$c LogEqbBody $.

log-eqb-body-syntax $a class ( LogEqbBody ) $.

${
  $d m p $.

  logipedia-nat-sym-eq-eqb-body-o $a |-
    A. p
      (
        (
          (
            m e. NN0 |->
              if ( m = 0 , 1 , 0 )
          )
          e.
          p
        )
        ->
        ( ( LogEqbBody ` 0 ) e. p )
      )
  $.
$}
