$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1968_b1: the probability that the minimum of two finite-valued
  integer random variables equals an integer k is the sum of their individual
  point probabilities minus the probability that their maximum equals k.
  No independence is assumed. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A set.mm probability measure P represents the arbitrary source probability
  space, whose sample space is U. dom P. The functions X and Y are real random
  variables with finite ranges contained in ZZ. Via the standard embedding of
  integers into reals, this is equivalent to the source's measurable
  finite-valued integer random variables.

  The two conditional terms are respectively min(X(x),Y(x)) and
  max(X(x),Y(x)). The final declaration is the single unproved $a corpus
  statement; there is no $p proof statement in this file.
$)

${
  $d P X Y k x $.

  putnambench-putnam-1968-b1 $a |- A. P e. Prob A. X A. Y A. k e. ZZ
    (
      (
        (
          X e. ( rRndVar ` P )
          /\
          (
            ran X C_ ZZ
            /\
            ran X e. Fin
          )
        )
        /\
        (
          Y e. ( rRndVar ` P )
          /\
          (
            ran Y C_ ZZ
            /\
            ran Y e. Fin
          )
        )
      )
      ->
      (
        P `
        { x e. U. dom P |
          if (
            ( X ` x ) <_ ( Y ` x ) ,
            ( X ` x ) ,
            ( Y ` x )
          )
          =
          k
        }
      )
      =
      (
        (
          ( P ` ( `' X " { k } ) )
          +
          ( P ` ( `' Y " { k } ) )
        )
        -
        (
          P `
          { x e. U. dom P |
            if (
              ( X ` x ) <_ ( Y ` x ) ,
              ( Y ` x ) ,
              ( X ` x )
            )
            =
            k
          }
        )
      )
    )
  $.
$}
