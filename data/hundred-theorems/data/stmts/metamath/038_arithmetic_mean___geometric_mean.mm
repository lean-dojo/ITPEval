$(
  Statement-only formalization of "Arithmetic Mean / Geometric Mean" from
  Hundred Theorems item 038: for every nonempty finite prefix of a
  nonnegative real sequence, the product is at most the corresponding power
  of its arithmetic mean. This file contains no proof.
$)

$[ library/set.mm $]

$(
  All mathematical notation in the assertion is defined by set.mm. The
  function F is an arbitrary real sequence indexed by the positive natural
  numbers. Restricting it to 1 ... N therefore represents an arbitrary
  N-tuple, without replacing the sequence by a finite table.

  This is the power form of AM-GM used directly by the HOL Light and Rocq
  sources. The zero-based source formulation is obtained by successor
  reindexing. For positive N and nonnegative entries, this form is
  equivalent to the usual N-th-root comparison because raising
  nonnegative reals to the positive natural power N is order preserving.

  The final $a assertion records only the statement; there is no $p proof.
$)

hundred-theorems-038-arithmetic-geometric-mean $a
  |- ( F : NN --> RR ->
       A. N e. NN
         ( ( A. k e. ( 1 ... N ) 0 <_ ( F ` k ) ) ->
           ( prod_ k e. ( 1 ... N ) ( F ` k ) ) <_
             ( ( ( sum_ k e. ( 1 ... N ) ( F ` k ) ) / N ) ^ N ) ) )
$.
