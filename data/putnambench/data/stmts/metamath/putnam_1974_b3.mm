$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_b3: a real number whose cosine after multiplication by pi is
  one third is irrational. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR and QQ are SetMM's standard classes of real and rational numbers.
  The functions cos and _pi and the arithmetic operations are the standard
  real cosine, pi, multiplication, and division supplied by set.mm.

  The restricted universal quantifier preserves the arbitrary real parameter
  from the sources, and non-membership in QQ is exactly irrationality for a
  real number. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

putnambench-putnam-1974-b3 $a |- A. x e. RR
  (
    ( cos ` ( _pi x. x ) ) = ( 1 / 3 )
    ->
    x e/ QQ
  )
$.
