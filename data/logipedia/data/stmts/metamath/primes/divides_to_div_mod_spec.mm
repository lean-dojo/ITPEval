$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_to_div_mod_spec
  (logipedia__metamath__primes.divides_to_div_mod_spec), catalog title
  "primes.divides_to_div_mod_spec": a positive natural divisor of a natural
  number yields the division-with-remainder specification with the source
  quotient and remainder zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For NN0 values, SetMM's n || m is equivalent to the
  source relation primes.divides n m, characterized by a natural multiplier
  q with m = n x. q.

  The source introduction and elimination declarations make
  div_mod_spec m n q r logically equivalent to

    r < n /\ m = (q x. n) + r.

  The inline conditional is exactly the source div_mod.div m n: at divisor
  zero it returns m + 1, while at a positive divisor it is the usual natural
  quotient, represented by SetMM floor. Thus the conclusion is a
  bidirectionally equivalent expansion of the source predicate with its
  original quotient argument. The restricted quantifiers and nested
  implications preserve the source scopes and assumptions. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-primes-divides-to-div-mod-spec $a |-
    A. n e. NN0 A. m e. NN0
      (
        0 < n
        ->
        (
          n || m
          ->
          (
            0 < n
            /\
            m =
              (
                (
                  if (
                    n = 0 ,
                    ( m + 1 ) ,
                    ( |_ ` ( m / n ) )
                  )
                  x. n
                )
                + 0
              )
          )
        )
      )
  $.
$}
