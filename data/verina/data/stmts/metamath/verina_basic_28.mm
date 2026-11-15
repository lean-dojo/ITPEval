$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_28
  (verina__metamath__verina_basic_28), catalog title isPrime: the exact
  fuel-bounded executable natural-number divisor search returns a Boolean
  primality decision under the n >= 2 precondition and satisfies its
  all-divisors/exists-divisor correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and { 0 , 1 } represents
  Bool with false = 0 and true = 1. VERINAB28NatMod explicitly reproduces
  Lean Nat.mod on all natural divisors, including n % 0 = n, rather than
  relying on SetMM's remainder convention at zero. VERINAB28State is the
  pair (i, fuel) used by the source local check function.

  VERINAB28Continue is exactly the recursive branch after the source tests
  fuel = 0, i * i > n, and n % i = 0 have all returned false. It increments
  i and decrements the positive fuel. VERINAB28Stop preserves that test
  priority: exhausted fuel returns true, an index whose square exceeds n
  returns true, and an in-range divisor returns false.

  VERINAB28CheckGraph records the complete finite execution trace from an
  arbitrary source check call, and VERINAB28Check selects its unique Boolean
  result. VERINAB28IsPrime invokes that exact computation at i = 2 with fuel
  n, matching both the source bound let-binding and the proof-irrelevant
  precondition argument. Thus the executable output is fixed independently
  of the postcondition and the graph admits no extra result.

  VERINAB28Pre is exactly n >= 2. Under this precondition, SetMM's half-open
  natural interval 2 ..^ n is exactly List.range' 2 (n - 2).
  VERINAB28Post reproduces both source Boolean implications using the same
  exact Nat.mod operation: true requires every candidate to have nonzero
  remainder, while false requires some candidate to divide n. The
  proof-valued precondition arguments to the implementation and postcondition
  have no computational or propositional effect beyond the explicit
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB28NatMod VERINAB28State
  VERINAB28Continue VERINAB28Stop
  VERINAB28CheckGraph VERINAB28Check
  VERINAB28Pre VERINAB28IsPrime VERINAB28Post
$.

verinab28-nat-mod-syntax
  $a class ( VERINAB28NatMod A B ) $.
verinab28-state-syntax
  $a class VERINAB28State $.
verinab28-continue-syntax
  $a wff ( VERINAB28Continue A B C ) $.
verinab28-stop-syntax
  $a wff ( VERINAB28Stop A B C ) $.
verinab28-check-graph-syntax
  $a wff ( VERINAB28CheckGraph A B C D ) $.
verinab28-check-syntax
  $a class ( VERINAB28Check A B C ) $.
verinab28-precondition-syntax
  $a wff ( VERINAB28Pre A ) $.
verinab28-is-prime-syntax
  $a class ( VERINAB28IsPrime A ) $.
verinab28-postcondition-syntax
  $a wff ( VERINAB28Post A B ) $.

verinab28-nat-mod-definition $a |- (
  VERINAB28NatMod A B
) = if (
  B = 0 ,
  A ,
  ( A mod B )
) $.

verinab28-state-definition $a |- VERINAB28State = (
  NN0 X. NN0
) $.

verinab28-continue-definition $a |- (
  VERINAB28Continue A B C
) <-> (
  (
    (
      A e. NN0
      /\
      B e. VERINAB28State
    )
    /\
    C e. VERINAB28State
  )
  /\
  (
    (
      (
        ( 2nd ` B ) =/= 0
        /\
        (
          ( 1st ` B ) x. ( 1st ` B )
        ) <_ A
      )
      /\
      (
        VERINAB28NatMod A ( 1st ` B )
      ) =/= 0
    )
    /\
    C = <.
      ( ( 1st ` B ) + 1 ) ,
      ( ( 2nd ` B ) - 1 )
    >.
  )
) $.

verinab28-stop-definition $a |- (
  VERINAB28Stop A B C
) <-> (
  (
    (
      A e. NN0
      /\
      B e. VERINAB28State
    )
    /\
    C e. { 0 , 1 }
  )
  /\
  (
    (
      ( 2nd ` B ) = 0
      /\
      C = 1
    )
    \/
    (
      (
        ( 2nd ` B ) =/= 0
        /\
        A < (
          ( 1st ` B ) x. ( 1st ` B )
        )
      )
      /\
      C = 1
    )
    \/
    (
      (
        (
          ( 2nd ` B ) =/= 0
          /\
          (
            ( 1st ` B ) x. ( 1st ` B )
          ) <_ A
        )
        /\
        (
          VERINAB28NatMod A ( 1st ` B )
        ) = 0
      )
      /\
      C = 0
    )
  )
) $.

${
  $d j k t A B C D $.

  verinab28-check-graph-definition $a |- (
    VERINAB28CheckGraph A B C D
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
    E. k e. NN0 E. t e. Word VERINAB28State
      (
        (
          ( # ` t ) = ( k + 1 )
          /\
          ( t ` 0 ) = <. B , C >.
        )
        /\
        (
          A. j e. ( 0 ..^ k )
            (
              VERINAB28Continue
                A
                ( t ` j )
                ( t ` ( j + 1 ) )
            )
          /\
          (
            VERINAB28Stop
              A
              ( t ` k )
              D
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab28-check-definition $a |- (
    VERINAB28Check A B C
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB28CheckGraph A B C y )
  ) $.
$}

verinab28-precondition-definition $a |- (
  VERINAB28Pre A
) <-> (
  (
    A e. NN0
    /\
    2 <_ A
  )
) $.

verinab28-is-prime-definition $a |- (
  VERINAB28IsPrime A
) = (
  VERINAB28Check A 2 A
) $.

${
  $d k A B $.

  verinab28-postcondition-definition $a |- (
    VERINAB28Post A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      (
        B = 1
        ->
        A. k e. ( 2 ..^ A )
          (
            VERINAB28NatMod A k
          ) =/= 0
      )
      /\
      (
        B = 0
        ->
        E. k e. ( 2 ..^ A )
          (
            VERINAB28NatMod A k
          ) = 0
      )
    )
  ) $.
$}

verina-basic-28-is-prime $a |- A. n e. NN0
  (
    ( VERINAB28Pre n )
    ->
    (
      VERINAB28Post
        n
        ( VERINAB28IsPrime n )
    )
  )
$.
