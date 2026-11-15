$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_diff: a Boolean-filtered finite product of natural numbers
  factors as the selected value times the product with that selected index
  excluded. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain and {0,1} is the Boolean carrier,
  with true represented by 1. The half-open interval 0 ..^ n contains
  exactly the source indices below n. Restricting the finite product to
  p(x) = 1 represents bigop n p 1 times f, while additionally requiring
  i =/= x represents andb (notb (eqb i x)) (p x) = true. Thus the displayed
  products are definitionally equivalent to the two source bigop terms.
  The final declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

${
  $d f i n p x $.

  logipedia-bigops-bigop-diff $a |-
    A. p e. ( { 0 , 1 } ^m NN0 )
      A. f e. ( NN0 ^m NN0 )
        A. i e. NN0
          A. n e. NN0
            (
              i < n
              ->
              (
                ( p ` i ) = 1
                ->
                (
                  prod_ x e.
                    {
                      x e. ( 0 ..^ n )
                      |
                      ( p ` x ) = 1
                    }
                    ( f ` x )
                )
                =
                (
                  ( f ` i )
                  x.
                  (
                    prod_ x e.
                      {
                        x e. ( 0 ..^ n )
                        |
                        (
                          i =/= x
                          /\
                          ( p ` x ) = 1
                        )
                      }
                      ( f ` x )
                  )
                )
              )
            )
  $.
$}
