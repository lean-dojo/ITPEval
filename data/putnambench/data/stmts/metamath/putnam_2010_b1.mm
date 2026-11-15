$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_b1: there is no infinite sequence of real numbers whose
  mth-power series sums to m for every positive integer m. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is SetMM's class of real-valued sequences indexed by the
  nonnegative integers, and NN is the class of positive integers. The
  arbitrary-index sum over NN0 is SetMM's infinite real-series sum, matching
  Lean's totalized infinite sum and Rocq's real-series operator. This follows
  the published infinite-series problem and its primary Lean formalization;
  Isabelle's finite-set sum notation over the infinite natural carrier is a
  secondary transcription defect.

  The sources state that the existential proposition is equivalent to False.
  The final negated existential is bidirectionally logically equivalent to
  that biconditional. It keeps the sequence witness internally existential
  and quantifies over every positive exponent. The declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d a i m $.

  putnambench-putnam-2010-b1 $a |- -.
    E. a e. ( RR ^m NN0 )
      A. m e. NN
        ( sum_ i e. NN0 ( ( a ` i ) ^ m ) ) = m
  $.
$}
