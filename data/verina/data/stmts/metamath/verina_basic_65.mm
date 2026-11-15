$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_65
  (verina__metamath__verina_basic_65), catalog title SquareRoot: the exact
  bounded natural-number recursion computes the integer square root and
  satisfies its two-sided square-bound correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain.

  VERINAB65LoopGraph is the exact graph of the source local boundedLoop for
  an arbitrary input N, remaining bound, and current candidate r. Its witness
  p is the number of recursive increment branches taken. It is at most the
  remaining bound; every one of those p branches satisfies
  (r+j+1)*(r+j+1) <= N; and when p is smaller than the bound, the next branch
  condition is false. The result is exactly r+p. Thus bound zero returns r,
  while a positive bound either increments and recurses or stops at the first
  failed square test, with no additional outputs. VERINAB65Loop selects this
  unique result.

  VERINAB65Pre is the source True precondition together with the Nat input
  type. VERINAB65SquareRoot is exactly the executable source call
  boundedLoop (N+1) 0. VERINAB65Post is the source postcondition:
  result*result <= N and N < (result+1)*(result+1). The proof-valued
  precondition arguments are computationally and propositionally unused and
  are represented by the explicit precondition antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB65LoopGraph VERINAB65Loop
  VERINAB65Pre VERINAB65SquareRoot VERINAB65Post
$.

verinab65-loop-graph-syntax
  $a wff ( VERINAB65LoopGraph A B C D ) $.
verinab65-loop-syntax
  $a class ( VERINAB65Loop A B C ) $.
verinab65-precondition-syntax
  $a wff ( VERINAB65Pre A ) $.
verinab65-program-syntax
  $a class ( VERINAB65SquareRoot A ) $.
verinab65-postcondition-syntax
  $a wff ( VERINAB65Post A B ) $.

${
  $d j p A B C D $.

  verinab65-loop-graph-definition $a |- (
    VERINAB65LoopGraph A B C D
  ) <-> (
    (
      (
        (
          A e. NN0
          /\
          B e. NN0
        )
        /\
        C e. NN0
      )
      /\
      D e. NN0
    )
    /\
    E. p e. NN0
      (
        p <_ B
        /\
        (
          A. j e. ( 0 ..^ p )
            (
              (
                ( ( C + j ) + 1 )
                x.
                ( ( C + j ) + 1 )
              ) <_ A
            )
          /\
          (
            p < B
            ->
            A < (
              ( ( C + p ) + 1 )
              x.
              ( ( C + p ) + 1 )
            )
          )
          /\
          D = ( C + p )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab65-loop-definition $a |- (
    VERINAB65Loop A B C
  ) = (
    iota_ y e. NN0
      ( VERINAB65LoopGraph A B C y )
  ) $.
$}

verinab65-precondition-definition $a |- (
  VERINAB65Pre A
) <-> (
  A e. NN0
) $.

verinab65-program-definition $a |- (
  VERINAB65SquareRoot A
) = (
  VERINAB65Loop A ( A + 1 ) 0
) $.

verinab65-postcondition-definition $a |- (
  VERINAB65Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    ( B x. B ) <_ A
    /\
    A < ( ( B + 1 ) x. ( B + 1 ) )
  )
) $.

verina-basic-65-square-root $a |- A. n e. NN0
  (
    ( VERINAB65Pre n )
    ->
    (
      VERINAB65Post
        n
        ( VERINAB65SquareRoot n )
    )
  )
$.
