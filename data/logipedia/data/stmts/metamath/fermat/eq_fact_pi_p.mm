$(
  Statement-only formalization of the Logipedia corpus artifact
  fermat.eq_fact_pi_p (logipedia__metamath__fermat.eq_fact_pi_p), catalog
  title "fermat.eq_fact_pi_p": every natural number's factorial equals the
  finite product of the positive integers up to that number. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves the source natural-number domain. Since source natural
  subtraction gives (S n) - 1 = n, and its bigop with base one,
  multiplication, an always-true filter, and term i + 1 ranges over indices
  below n, the right side is exactly the product over 0 ..^ n. SetMM's !
  is the corresponding factorial function. The declaration is an unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

${
  $d i n $.

  logipedia-fermat-eq-fact-pi-p $a |-
    A. n e. NN0
      (
        ( ! ` n )
        =
        prod_ i e. ( 0 ..^ n ) ( i + 1 )
      )
  $.
$}
