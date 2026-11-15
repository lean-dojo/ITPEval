$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.let_clause_1531
  (logipedia__metamath__primes.let_clause_1531), catalog title
  "primes.let_clause_1531": if a positive natural number m is divisible by n
  and equals n times zero, then m equals zero, with the source's universally
  quantified natural d retained. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For n and m in NN0, SetMM's n || m is equivalent to
  the source relation primes.divides n m, characterized by a natural
  multiplier q satisfying m = n x. q. SetMM's native order,
  multiplication, and equality represent nat.lt, nat.times, and logic.eq.
  The restricted universal quantifiers and nested implications preserve the
  source binder order, including the unused binder d, assumptions,
  conclusion, and all scopes. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d d m n $.

  logipedia-primes-let-clause-1531 $a |-
    A. n e. NN0
      A. m e. NN0
        (
          0 < m
          ->
          (
            n || m
            ->
            A. d e. NN0
              (
                m = ( n x. 0 )
                ->
                m = 0
              )
          )
        )
  $.
$}
