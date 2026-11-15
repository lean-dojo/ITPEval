$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_b4: symmetry in the number of integer tuples whose sum of
  absolute coordinate values is bounded by a positive integer. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers. For n in NN, the class
  ZZ ^m ( 1 ... n ) consists of all integer-valued functions on the
  one-based n-element index interval, hence is exactly the set of integer
  n-tuples. The restricted class retains precisely those tuples whose finite
  sum of coordinate absolute values is at most m.

  The ground-truth statements introduce a function f and assume, for every
  positive pair (m,n), that f(m,n) is the cardinality displayed here.
  Substituting that definition into f(m,n) = f(n,m) gives this assertion.
  Conversely, this assertion makes every function satisfying that defining
  assumption symmetric, so the direct cardinality formulation is
  bidirectionally equivalent to the source theorem. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d i m n x $.

  putnambench-putnam-2005-b4 $a |- A. m e. NN
    A. n e. NN
      (
        (
          #
          `
          {
            x e. ( ZZ ^m ( 1 ... n ) )
            |
            (
              sum_ i e. ( 1 ... n )
                ( abs ` ( x ` i ) )
            )
            <_
            m
          }
        )
        =
        (
          #
          `
          {
            x e. ( ZZ ^m ( 1 ... m ) )
            |
            (
              sum_ i e. ( 1 ... m )
                ( abs ` ( x ` i ) )
            )
            <_
            n
          }
        )
      )
  $.
$}
