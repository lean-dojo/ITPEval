$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_to_minus (logipedia__metamath__nat.le_plus_to_minus), catalog
  title "nat.le_plus_to_minus": for all natural numbers n, m, and p, if n is
  at most p plus m, then the truncated difference n minus m is at most p.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition and non-strict order represent
  nat.plus and nat.le. For natural numbers n and m, the term
  if ( m <_ n , n - m , 0 ) exactly represents the source total subtraction
  nat.minus n m: ordinary subtraction when m is at most n, and zero otherwise.
  The three restricted universal quantifiers and implication preserve the
  source binder order, scopes, assumption, and conclusion. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-le-plus-to-minus $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        (
          n <_ ( p + m )
          ->
          if (
            m <_ n ,
            ( n - m ) ,
            0
          )
          <_
          p
        )
$.
