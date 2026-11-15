$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_48
  (verina__metamath__verina_basic_48), catalog title isPerfectSquare: the
  exact fuel-bounded natural-number search decides whether its input is a
  perfect square and satisfies its Boolean correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and { 0 , 1 } represents
  Bool with false = 0 and true = 1.

  VERINAB48CheckGraph is the exact finite execution graph of the source local
  recursive helper check for every natural input n, candidate x, and fuel.
  Its Boolean trace has fuel + 1 entries. The terminal entry is false, exactly
  matching the zero-fuel branch. Reading backward, each preceding entry first
  returns false when (x + k)^2 exceeds n, then returns true when it equals n,
  and otherwise uses the next trace entry. Thus VERINAB48Check selects the
  unique result of the same guard order and recursive call
  check (x + 1) remainingFuel.

  VERINAB48IsPerfectSquare preserves the source zero branch and otherwise
  invokes check at candidate one with fuel n. VERINAB48Pre is the source True
  precondition together with the Nat input type. VERINAB48Post identifies
  Boolean truth exactly with the existence of a natural square root. The
  proof-valued precondition arguments are computationally and propositionally
  unused beyond the explicit antecedent in the final correctness assertion.
  The source check_correct and check_complete declarations are proof-only
  auxiliaries and are not part of this statement package. Every earlier $a is
  syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB48CheckGraph VERINAB48Check
  VERINAB48Pre VERINAB48IsPerfectSquare VERINAB48Post
$.

verinab48-check-graph-syntax
  $a wff ( VERINAB48CheckGraph A B C D ) $.
verinab48-check-syntax
  $a class ( VERINAB48Check A B C ) $.
verinab48-precondition-syntax
  $a wff ( VERINAB48Pre A ) $.
verinab48-program-syntax
  $a class ( VERINAB48IsPerfectSquare A ) $.
verinab48-postcondition-syntax
  $a wff ( VERINAB48Post A B ) $.

${
  $d k t A B C D $.

  verinab48-check-graph-definition $a |- (
    VERINAB48CheckGraph A B C D
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
      D e. { 0 , 1 }
    )
    /\
    E. t e. Word { 0 , 1 }
      (
        (
          ( # ` t ) = ( C + 1 )
          /\
          ( t ` C ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ C )
            ( t ` k ) = if (
              A < (
                ( B + k )
                x.
                ( B + k )
              ) ,
              0 ,
              if (
                (
                  ( B + k )
                  x.
                  ( B + k )
                ) = A ,
                1 ,
                ( t ` ( k + 1 ) )
              )
            )
          /\
          D = ( t ` 0 )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab48-check-definition $a |- (
    VERINAB48Check A B C
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB48CheckGraph A B C y )
  ) $.
$}

verinab48-precondition-definition $a |- (
  VERINAB48Pre A
) <-> (
  A e. NN0
) $.

verinab48-program-definition $a |- (
  VERINAB48IsPerfectSquare A
) = if (
  A = 0 ,
  1 ,
  ( VERINAB48Check A 1 A )
) $.

${
  $d i A B $.

  verinab48-postcondition-definition $a |- (
    VERINAB48Post A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      B = 1
      <->
      E. i e. NN0
        ( i x. i ) = A
    )
  ) $.
$}

verina-basic-48-is-perfect-square $a |- A. n e. NN0
  (
    ( VERINAB48Pre n )
    ->
    (
      VERINAB48Post
        n
        ( VERINAB48IsPerfectSquare n )
    )
  )
$.
