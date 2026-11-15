$(
  Statement-only formalization of Thousand Theorems corpus artifact Q282649
  (thousand-theorems__metamath__Q282649), "Pentagonal number theorem": over
  every commutative ring with an arbitrary topology on its carrier, the
  finite-subset net of products of the formal power series
  1 - X^(n + 1) converges in the coefficientwise product topology to the
  signed series supported on the generalized pentagonal numbers. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A formal power series over R is represented extensionally by its coefficient
  function NN0 --> Base(R). Q282649Partial R S is the coefficient function of

    product_(n in S) (1 - X^(n + 1)).

  Its kth coefficient is the sum over subsets T of S whose selected exponents
  sum to k, with sign (-1)^|T|. This is the finite distributive expansion of
  the product and is valid over every commutative ring.

  Q282649PentIndex k is the unique n >= 0 for which k is one of

    n(3n - 1)/2  or  n(3n + 1)/2.

  These two branches respectively encode the nonnegative and negative integer
  indices in k(3k - 1)/2. Since (-1)^(-n) = (-1)^n, Q282649Series R is exactly
  the source pentagonalSeries coefficient function.

  Q282649HasProd R J expands HasProd as convergence of the net indexed by
  finite subsets of NN0 ordered by inclusion. The topology is SetMM's indexed
  product of the arbitrary coefficient topology J, exactly the Pi topology on
  formal power series used by PowerSeries.WithPiTopology.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or transparent definitions, and this
  database contains no $p proof declaration.
$)

$c Q282649Partial Q282649PentIndex Q282649Series Q282649HasProd $.

q282649-partial-syntax
  $a class ( Q282649Partial R S ) $.
q282649-pentagonal-index-syntax
  $a class ( Q282649PentIndex k ) $.
q282649-series-syntax
  $a class ( Q282649Series R ) $.
q282649-has-product-syntax
  $a wff ( Q282649HasProd R J ) $.

${
  $d R S T k n $.

  q282649-partial-definition $a |- (
    Q282649Partial R S
  ) = (
    k e. NN0 |->
      R gsum
        (
          T e.
            {
              T e. ~P S |
              ( sum_ n e. T ( n + 1 ) ) = k
            }
          |->
            (
              ( # ` T )
              ( .g ` ( mulGrp ` R ) )
              ( ( -g ` R ) ` ( 1r ` R ) )
            )
        )
  ) $.
$}

${
  $d k n $.

  q282649-pentagonal-index-definition $a |- (
    Q282649PentIndex k
  ) = (
    iota_ n e. NN0
      (
        ( 2 x. k ) = ( n x. ( ( 3 x. n ) - 1 ) )
        \/
        ( 2 x. k ) = ( n x. ( ( 3 x. n ) + 1 ) )
      )
  ) $.
$}

${
  $d R k n $.

  q282649-series-definition $a |- (
    Q282649Series R
  ) = (
    k e. NN0 |->
      if (
        E. n e. NN0
          (
            ( 2 x. k ) = ( n x. ( ( 3 x. n ) - 1 ) )
            \/
            ( 2 x. k ) = ( n x. ( ( 3 x. n ) + 1 ) )
          )
        ,
        (
          ( Q282649PentIndex k )
          ( .g ` ( mulGrp ` R ) )
          ( ( -g ` R ) ` ( 1r ` R ) )
        )
        ,
        ( 0g ` R )
      )
  ) $.
$}

${
  $d J O R S T n $.

  q282649-has-product-definition $a |- (
    ( Q282649HasProd R J )
    <->
    A. O e. ( Xt_ ` ( n e. NN0 |-> J ) )
      (
        ( Q282649Series R ) e. O
        ->
        E. S e. ( ~P NN0 i^i Fin )
          A. T e. ( ~P NN0 i^i Fin )
            (
              S C_ T
              ->
              ( Q282649Partial R T ) e. O
            )
      )
  ) $.
$}

${
  $d J R $.

  thousand-theorems-q282649-pentagonal-number-theorem $a |-
    A. R e. CRing
      A. J e. ( TopOn ` ( Base ` R ) )
        ( Q282649HasProd R J )
  $.
$}
