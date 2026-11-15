$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_b5: counting endofunctions of {1, ..., n} for which every
  orbit eventually reaches a value at most k. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The inclusive interval 1 ... n is the source set X. Thus f ranges over
  every endofunction of X, without extending or restricting its domain.
  IterComp is set.mm's native finite-iteration operator, including the
  identity iterate at j = 0. The internally existential j therefore states
  exactly that each orbit eventually reaches an element at most k.

  The restricted class contains precisely the endofunctions satisfying that
  orbit condition, and # is its finite cardinality. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d f j k n x $.

  putnambench-putnam-2013-b5 $a |- A. n e. NN A. k e. ( 1 ... n )
    (
      #
      `
      {
        f e. ( ( 1 ... n ) ^m ( 1 ... n ) )
        |
        A. x e. ( 1 ... n ) E. j e. NN0
          (
            (
              ( ( IterComp ` f ) ` j )
              `
              x
            )
            <_
            k
          )
      }
    )
    =
    (
      k
      x.
      ( n ^ ( n - 1 ) )
    )
  $.
$}
