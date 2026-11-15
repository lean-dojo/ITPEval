$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.mod_O_to_divides
  (logipedia__metamath__primes.mod_O_to_divides), catalog title
  "primes.mod_O_to_divides": for a positive natural number n, remainder zero
  on division of a natural number m by n implies that n divides m. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Under the assumption 0 < n, SetMM's m mod n is
  exactly the source total natural remainder div_mod.mod m n. For n and m in
  NN0, SetMM's n || m is equivalent to the source relation primes.divides n m,
  characterized by a natural multiplier q satisfying m = n x. q. The
  restricted universal quantifiers and nested implications preserve the
  source binder order, assumptions, conclusion, and all scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

${
  $d m n $.

  logipedia-primes-mod-O-to-divides $a |-
    A. n e. NN0
      A. m e. NN0
        (
          0 < n
          ->
          (
            ( m mod n ) = 0
            ->
            n || m
          )
        )
  $.
$}
