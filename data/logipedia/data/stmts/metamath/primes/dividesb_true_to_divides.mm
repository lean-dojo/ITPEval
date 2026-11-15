$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.dividesb_true_to_divides
  (logipedia__metamath__primes.dividesb_true_to_divides), catalog title
  "primes.dividesb_true_to_divides": for natural numbers n and m, if the
  Boolean divisibility test of n into m returns true, then n divides m. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents both source
  natural-number domains. For n and m in NN0, SetMM's n || m is equivalent to
  the source relation primes.divides n m, characterized by a natural
  multiplier q satisfying m = n x. q. The source total remainder
  div_mod.mod m n equals m when n = 0 and otherwise equals SetMM's m mod n,
  so if ( n = 0 , m , ( m mod n ) ) represents it on the full source domain.
  The Boolean carrier is {0,1}, true is 1, and the outer conditional is
  exactly the source equality dividesb n m = true. The restricted universal
  quantifiers and implication preserve the source binder order and scopes.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-primes-dividesb-true-to-divides $a |-
    A. n e. NN0
      A. m e. NN0
        (
          if (
            if ( n = 0 , m , ( m mod n ) ) = 0 ,
            1 ,
            0
          ) = 1
          ->
          n || m
        )
  $.
$}
