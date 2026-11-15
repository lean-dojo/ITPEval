$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.let_clause_15311
  (logipedia__metamath__primes.let_clause_15311), catalog title
  "primes.let_clause_15311": if a positive natural number m is divisible by n
  and equals n times the successor of p, then m equals n plus n times p, with
  the source's universally quantified natural d retained. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For n and m in NN0, SetMM's n || m is equivalent to
  the source relation primes.divides n m, characterized by a natural
  multiplier q satisfying m = n x. q. SetMM's 0 and p + 1 represent nat.O and
  nat.S p, while its native strict order, addition, multiplication, and
  equality represent nat.lt, nat.plus, nat.times, and logic.eq on this domain.
  The restricted universal quantifiers and nested implications preserve the
  source binder order, including the unused binder d, assumptions, conclusion,
  and all scopes. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d d m n p $.

  logipedia-primes-let-clause-15311 $a |-
    A. n e. NN0
      A. m e. NN0
        (
          0 < m
          ->
          (
            n || m
            ->
            A. d e. NN0
              A. p e. NN0
                (
                  m = ( n x. ( p + 1 ) )
                  ->
                  m = ( n + ( n x. p ) )
                )
          )
        )
  $.
$}
