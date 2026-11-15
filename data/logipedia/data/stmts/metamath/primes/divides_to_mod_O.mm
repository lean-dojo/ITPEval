$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_to_mod_O
  (logipedia__metamath__primes.divides_to_mod_O), catalog title
  "primes.divides_to_mod_O": a positive natural number that divides another
  natural number leaves remainder zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For n and m in NN0, SetMM's n || m is equivalent to
  the source relation primes.divides n m, characterized by a natural
  multiplier q satisfying m = n x. q. Under the assumption 0 < n, SetMM's
  m mod n is exactly the source total natural remainder div_mod.mod m n.
  The restricted universal quantifiers and nested implications preserve the
  source binder order, assumptions, conclusion, and all scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-primes-divides-to-mod-O $a |-
    A. n e. NN0
      A. m e. NN0
        (
          0 < n
          ->
          (
            n || m
            ->
            ( m mod n ) = 0
          )
        )
  $.
$}
