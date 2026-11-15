$(
  Statement-only formalization of "Sum of kth Powers" from Hundred Theorems
  corpus artifact 077 (hundred-theorems__metamath__077): Faulhaber's formula
  expresses each inclusive finite sum of nonnegative-integer powers using
  Bernoulli polynomials. This file contains no proof.
$)

$[ library/set.mm $]

$(
  NN0 is the class of nonnegative integers, and BernPoly is set.mm's
  recursively defined Bernoulli polynomial operator. For K,M in NN0, the
  finite-sum binder ranges n over 0 through M, so the left side is

    0^K + 1^K + ... + M^K.

  The assertion is the target-native form of the same Bernoulli-polynomial
  identity stated over the reals or rationals in the source formalizations.
  Its final declaration is an unproved $a statement.
$)

${
  $d K n $.  $d M n $.

  hundred-theorems-077-sum-of-kth-powers $a
    |- ( ( K e. NN0 /\ M e. NN0 ) ->
         sum_ n e. ( 0 ... M ) ( n ^ K ) =
         ( ( ( ( K + 1 ) BernPoly ( M + 1 ) ) -
               ( ( K + 1 ) BernPoly 0 ) ) /
           ( K + 1 ) ) )
  $.
$}
