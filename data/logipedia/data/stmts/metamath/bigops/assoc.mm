$(
  Statement-only formalization of the Logipedia corpus artifact bigops.assoc:
  multiplication of nonnegative natural numbers is associative. This file
  contains no proof.
$)

$[ lib/set.mm $]

logipedia-bigops-assoc $a
  |- A. a e. NN0 A. b e. NN0 A. c e. NN0
       ( ( a x. ( b x. c ) ) = ( ( a x. b ) x. c ) ) $.
