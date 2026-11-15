$(
  Statement-only formalization of the Logipedia corpus artifact
  fermat.congruent_exp_pred_SO
  (logipedia__metamath__fermat.congruent_exp_pred_SO), catalog title
  "fermat.congruent_exp_pred_SO": for natural numbers p and a, if p is prime
  and does not divide a, then a raised to the predecessor of p is congruent
  to one modulo p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves the source natural-number domains. Under the prime
  antecedent, p is greater than one, so p - 1 is the source predecessor of p
  and SetMM remainder is the source total remainder operation. SetMM
  exponentiation represents the source recursive exponentiation, p || a is
  the equivalent divisibility predicate, and congruence is expanded as
  equality of remainders modulo p.
$)

${
  $d a p $.
  logipedia-fermat-congruent-exp-pred-so $a |-
    A. p e. NN0 A. a e. NN0
      ( p e. Prime
        ->
        ( -. p || a
          -> ( ( a ^ ( p - 1 ) ) mod p ) = ( 1 mod p ) ) )
  $.
$}
