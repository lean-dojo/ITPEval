$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.plus_minus_m_m (logipedia__metamath__nat.plus_minus_m_m), catalog title
  "nat.plus_minus_m_m": for all natural numbers n and m, if m is at most n,
  then n equals the truncated natural difference n minus m plus m. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition and non-strict order represent
  nat.plus and nat.le. For natural numbers n and m, the term
  if ( m <_ n , n - m , 0 ) exactly represents the source total subtraction
  nat.minus n m: ordinary subtraction when m is at most n, and zero otherwise.
  Native equality represents logic.eq at the natural-number type. The two
  restricted universal quantifiers, implication, and equality preserve the
  source binder order, scopes, assumption, and conclusion. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-plus-minus-m-m $a |-
  A. n e. NN0
    A. m e. NN0
      (
        m <_ n
        ->
        n
        =
        (
          if (
            m <_ n ,
            ( n - m ) ,
            0
          )
          +
          m
        )
      )
$.
