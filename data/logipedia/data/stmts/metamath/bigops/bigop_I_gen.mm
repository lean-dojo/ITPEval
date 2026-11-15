$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_I_gen: shifting a filtered finite product over nonnegative
  naturals agrees with filtering the original initial interval. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The source Boolean predicate and natural-valued function remain arbitrary
  total functions on NN0. The half-open interval 0 ..^ k represents the
  indices below k, and restricting a product to predicate value 1 represents
  the source bigop filter. Thus the two products directly encode the source
  bigop calls at b - a and b. The final declaration is an unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d a b f i p $.

  logipedia-bigops-bigop-i-gen $a |-
    A. a e. NN0
      A. b e. NN0
        A. p e. ( { 0 , 1 } ^m NN0 )
          A. f e. ( NN0 ^m NN0 )
            (
              a <_ b
              ->
              (
                prod_ i e.
                  {
                    i e. ( 0 ..^ ( b - a ) )
                    |
                    ( p ` ( i + a ) ) = 1
                  }
                  ( f ` ( i + a ) )
              )
              =
              (
                prod_ i e.
                  {
                    i e. ( 0 ..^ b )
                    |
                    (
                      a <_ i
                      /\
                      ( p ` i ) = 1
                    )
                  }
                  ( f ` i )
              )
            )
  $.
$}
