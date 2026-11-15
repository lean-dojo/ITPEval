$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.lt_mod_m_m (logipedia__metamath__div_mod.lt_mod_m_m), catalog title
  "div_mod.lt_mod_m_m": for all natural numbers n and positive m, the source
  remainder of n modulo m is less than m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The inline conditional is exactly
  div_mod.mod: at divisor zero it returns n, while at a positive divisor it is
  the usual natural remainder. The hypothesis 0 < m preserves the source
  positivity assumption and selects the positive-divisor branch. The
  declaration is an unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

${
  $d m n $.

  logipedia-div-mod-lt-mod-m-m $a |-
    A. n e. NN0 A. m e. NN0
      (
        0 < m
        ->
        if (
          m = 0 ,
          n ,
          ( n mod m )
        )
        <
        m
      )
  $.
$}
