$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_10, catalog title findExponents: repeated exact division by
  a nonempty distinct list of primes computes every prime exponent and
  reconstructs the positive input number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, Word NN0 is exactly the type
  of arbitrary finite natural-number lists, and Word ( NN0 X. NN0 ) is the
  corresponding type of finite lists of natural-number pairs.

  VERINA10CountFactorGraph is an exact closed-form graph of countFactor. When
  n is positive and p exceeds one, its unique exponent e and residual r
  satisfy n = p^e r and r mod p is nonzero; this is precisely the terminal
  state reached by repeatedly dividing by p while divisibility holds. In all
  other cases the source immediately returns the initial count and n.
  VERINA10RemovePrimeFactor is the residual from the same computation.

  VERINA10RemoveAllGraph threads removePrimeFactor through the prime word in
  left-to-right order, exactly reproducing foldl. VERINA10FindGraph similarly
  threads the residual through countFactor and records each input prime with
  its computed exponent, exactly reproducing countFactors. Thus the iota
  definitions admit one output only and preserve the executable program on
  every typed input, rather than merely selecting an output satisfying the
  postcondition. The Lean proof parameter is computationally unused, so the
  executable function needs no additional argument here; the final assertion
  is still guarded by the complete source precondition.

  VERINA10Product is the finite product of the recorded prime powers, equal
  to the source natural-number foldl from one. VERINA10Pre and VERINA10Post
  retain all type, positivity, nonemptiness, primality, duplicate-freedom,
  factor-removal, reconstruction, membership, and coverage clauses. The last
  $a declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA10CountFactorGraph VERINA10CountFactor
  VERINA10RemovePrimeFactor
  VERINA10RemoveAllGraph VERINA10RemoveAllPrimeFactors
  VERINA10Pre
  VERINA10FindGraph VERINA10FindExponents
  VERINA10Product VERINA10Post
$.

verina10-count-factor-graph-syntax
  $a wff ( VERINA10CountFactorGraph A B C D ) $.
verina10-count-factor-syntax
  $a class ( VERINA10CountFactor A B C ) $.
verina10-remove-prime-factor-syntax
  $a class ( VERINA10RemovePrimeFactor A B ) $.
verina10-remove-all-graph-syntax
  $a wff ( VERINA10RemoveAllGraph A B C ) $.
verina10-remove-all-prime-factors-syntax
  $a class ( VERINA10RemoveAllPrimeFactors A B ) $.
verina10-precondition-syntax
  $a wff ( VERINA10Pre A B ) $.
verina10-find-graph-syntax
  $a wff ( VERINA10FindGraph A B C ) $.
verina10-find-exponents-syntax
  $a class ( VERINA10FindExponents A B ) $.
verina10-product-syntax
  $a class ( VERINA10Product A ) $.
verina10-postcondition-syntax
  $a wff ( VERINA10Post A B C ) $.

${
  $d e r A B C D $.

  verina10-count-factor-graph-definition $a |- (
    VERINA10CountFactorGraph A B C D
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. ( NN0 X. NN0 )
      )
    )
    /\
    (
      (
        (
          0 < A
          /\
          1 < B
        )
        /\
        E. e e. NN0 E. r e. NN0
          (
            (
              A = ( ( B ^ e ) x. r )
              /\
              ( r mod B ) =/= 0
            )
            /\
            D = <. ( C + e ) , r >.
          )
      )
      \/
      (
        -.
        (
          0 < A
          /\
          1 < B
        )
        /\
        D = <. C , A >.
      )
    )
  ) $.
$}

${
  $d y A B C $.

  verina10-count-factor-definition $a |- (
    VERINA10CountFactor A B C
  ) = (
    iota_ y e. ( NN0 X. NN0 )
      ( VERINA10CountFactorGraph A B C y )
  ) $.
$}

verina10-remove-prime-factor-definition $a |- (
  VERINA10RemovePrimeFactor A B
) = (
  2nd ` ( VERINA10CountFactor A B 0 )
) $.

${
  $d k s A B C $.

  verina10-remove-all-graph-definition $a |- (
    VERINA10RemoveAllGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. Word NN0
      )
      /\
      C e. NN0
    )
    /\
    E. s e. Word NN0
      (
        (
          ( # ` s ) = ( ( # ` B ) + 1 )
          /\
          ( s ` 0 ) = A
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` B ) )
            (
              s ` ( k + 1 )
            ) = (
              VERINA10RemovePrimeFactor
                ( s ` k )
                ( B ` k )
            )
          /\
          C = ( s ` ( # ` B ) )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina10-remove-all-prime-factors-definition $a |- (
    VERINA10RemoveAllPrimeFactors A B
  ) = (
    iota_ y e. NN0
      ( VERINA10RemoveAllGraph A B y )
  ) $.
$}

${
  $d i j A B $.

  verina10-precondition-definition $a |- (
    VERINA10Pre A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. Word NN0
    )
    /\
    (
      (
        0 < A
        /\
        0 < ( # ` B )
      )
      /\
      (
        (
          A. i e. ( 0 ..^ ( # ` B ) )
            ( B ` i ) e. Prime
          /\
          A. i e. ( 0 ..^ ( # ` B ) )
            A. j e. ( 0 ..^ ( # ` B ) )
              (
                i =/= j
                ->
                ( B ` i ) =/= ( B ` j )
              )
        )
        /\
        ( VERINA10RemoveAllPrimeFactors A B ) = 1
      )
    )
  ) $.
$}

${
  $d k s A B C $.

  verina10-find-graph-definition $a |- (
    VERINA10FindGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. Word NN0
      )
      /\
      C e. Word ( NN0 X. NN0 )
    )
    /\
    (
      ( # ` C ) = ( # ` B )
      /\
      E. s e. Word NN0
        (
          (
            ( # ` s ) = ( ( # ` B ) + 1 )
            /\
            ( s ` 0 ) = A
          )
          /\
          A. k e. ( 0 ..^ ( # ` B ) )
            (
              (
                ( C ` k )
                =
                <.
                  ( B ` k )
                  ,
                  1st ` (
                    VERINA10CountFactor
                      ( s ` k )
                      ( B ` k )
                      0
                  )
                >.
              )
              /\
              (
                s ` ( k + 1 )
              ) = (
                2nd ` (
                  VERINA10CountFactor
                    ( s ` k )
                    ( B ` k )
                    0
                )
              )
            )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verina10-find-exponents-definition $a |- (
    VERINA10FindExponents A B
  ) = (
    iota_ y e. Word ( NN0 X. NN0 )
      ( VERINA10FindGraph A B y )
  ) $.
$}

${
  $d k A $.

  verina10-product-definition $a |- (
    VERINA10Product A
  ) = (
    prod_ k e. ( 0 ..^ ( # ` A ) )
      (
        ( 1st ` ( A ` k ) )
        ^
        ( 2nd ` ( A ` k ) )
      )
  ) $.
$}

${
  $d i j A B C $.

  verina10-postcondition-definition $a |- (
    VERINA10Post A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. Word NN0
      )
      /\
      C e. Word ( NN0 X. NN0 )
    )
    /\
    (
      A = ( VERINA10Product C )
      /\
      (
        A. i e. ( 0 ..^ ( # ` C ) )
          ( 1st ` ( C ` i ) ) e. ran B
        /\
        A. i e. ( 0 ..^ ( # ` B ) )
          E. j e. ( 0 ..^ ( # ` C ) )
            ( 1st ` ( C ` j ) ) = ( B ` i )
      )
    )
  ) $.
$}

verina-advanced-10-find-exponents $a |- A. n e. NN0
  A. p e. Word NN0
    (
      ( VERINA10Pre n p )
      ->
      (
        VERINA10Post
          n
          p
          ( VERINA10FindExponents n p )
      )
    )
$.
