$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_18, catalog title isArmstrong: exact decimal digit
  recursion decides whether a natural number equals the sum of its digits
  raised to its digit count, with its Boolean correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, Word NN0 is exactly the type
  of arbitrary finite natural-number lists, and { 0 , 1 } represents Bool
  with false = 0 and true = 1.

  VERINA18CountDigitsGraph is the exact finite execution graph of the local
  recursion in countDigits. Its trace repeatedly replaces a positive current
  value by its natural quotient by ten and stops at zero. The output is the
  number of divisions, except that the source's special initial accumulator
  makes the output one when the original input is zero.

  VERINA18SumPowersGraph is the exact finite execution graph of sumPowers.
  Its first trace performs the same repeated quotient-by-ten computation, and
  its second trace starts at zero and adds the current last decimal digit
  raised to the supplied exponent at each step. VERINA18CountDigits and
  VERINA18SumPowers select the unique outputs of these deterministic traces.

  VERINA18DecimalDigits is the unique canonical most-significant-first
  decimal digit word of a natural number, including the one-digit word
  containing zero for input zero. VERINA18DigitPowerSum is therefore exactly
  the source postcondition's fold over the character codes of toString after
  subtracting the code of '0'.

  VERINA18IsArmstrong is the source executable Boolean equality test, not an
  unconstrained function and not a result selected from the postcondition.
  VERINA18Pre is the source True precondition together with the Nat input
  type. VERINA18Post retains both source implications. The proof-valued
  precondition argument is computationally unused and is omitted from the
  target function. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no $p declaration.
$)

$c
  VERINA18CountDigitsGraph VERINA18CountDigits
  VERINA18SumPowersGraph VERINA18SumPowers
  VERINA18DecimalDigitsGraph VERINA18DecimalDigits
  VERINA18DigitPowerSum
  VERINA18Pre VERINA18IsArmstrong VERINA18Post
$.

verina18-count-digits-graph-syntax
  $a wff ( VERINA18CountDigitsGraph A B ) $.
verina18-count-digits-syntax
  $a class ( VERINA18CountDigits A ) $.
verina18-sum-powers-graph-syntax
  $a wff ( VERINA18SumPowersGraph A B C ) $.
verina18-sum-powers-syntax
  $a class ( VERINA18SumPowers A B ) $.
verina18-decimal-digits-graph-syntax
  $a wff ( VERINA18DecimalDigitsGraph A B ) $.
verina18-decimal-digits-syntax
  $a class ( VERINA18DecimalDigits A ) $.
verina18-digit-power-sum-syntax
  $a class ( VERINA18DigitPowerSum A ) $.
verina18-precondition-syntax
  $a wff ( VERINA18Pre A ) $.
verina18-is-armstrong-syntax
  $a class ( VERINA18IsArmstrong A ) $.
verina18-postcondition-syntax
  $a wff ( VERINA18Post A B ) $.

${
  $d i k s A B $.

  verina18-count-digits-graph-definition $a |- (
    VERINA18CountDigitsGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. NN0
    )
    /\
    E. k e. NN0 E. s e. Word NN0
      (
        (
          ( # ` s ) = ( k + 1 )
          /\
          ( s ` 0 ) = A
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              0 < ( s ` i )
              /\
              (
                s ` ( i + 1 )
              ) = (
                |_ ` ( ( s ` i ) / ; 1 0 )
              )
            )
          /\
          (
            ( s ` k ) = 0
            /\
            B = if ( A = 0 , 1 , k )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina18-count-digits-definition $a |- (
    VERINA18CountDigits A
  ) = (
    iota_ y e. NN0
      ( VERINA18CountDigitsGraph A y )
  ) $.
$}

${
  $d i k s t A B C $.

  verina18-sum-powers-graph-definition $a |- (
    VERINA18SumPowersGraph A B C
  ) <-> (
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
    E. k e. NN0 E. s e. Word NN0 E. t e. Word NN0
      (
        (
          (
            ( # ` s ) = ( k + 1 )
            /\
            ( # ` t ) = ( k + 1 )
          )
          /\
          (
            ( s ` 0 ) = A
            /\
            ( t ` 0 ) = 0
          )
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              0 < ( s ` i )
              /\
              (
                (
                  s ` ( i + 1 )
                ) = (
                  |_ ` ( ( s ` i ) / ; 1 0 )
                )
                /\
                (
                  t ` ( i + 1 )
                ) = (
                  ( t ` i )
                  +
                  ( ( ( s ` i ) mod ; 1 0 ) ^ B )
                )
              )
            )
          /\
          (
            ( s ` k ) = 0
            /\
            C = ( t ` k )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina18-sum-powers-definition $a |- (
    VERINA18SumPowers A B
  ) = (
    iota_ y e. NN0
      ( VERINA18SumPowersGraph A B y )
  ) $.
$}

${
  $d i A B $.

  verina18-decimal-digits-graph-definition $a |- (
    VERINA18DecimalDigitsGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. Word NN0
    )
    /\
    (
      ( # ` B ) = ( VERINA18CountDigits A )
      /\
      (
        A. i e. ( 0 ..^ ( # ` B ) )
          ( B ` i ) < ; 1 0
        /\
        (
          (
            0 < A
            ->
            0 < ( B ` 0 )
          )
          /\
          A = sum_ i e. ( 0 ..^ ( # ` B ) )
            (
              ( B ` i )
              x.
              (
                ; 1 0
                ^
                ( ( ( # ` B ) - 1 ) - i )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d y A $.

  verina18-decimal-digits-definition $a |- (
    VERINA18DecimalDigits A
  ) = (
    iota_ y e. Word NN0
      ( VERINA18DecimalDigitsGraph A y )
  ) $.
$}

${
  $d i A $.

  verina18-digit-power-sum-definition $a |- (
    VERINA18DigitPowerSum A
  ) = (
    sum_ i e. (
      0 ..^ ( # ` ( VERINA18DecimalDigits A ) )
    )
      (
        (
          ( VERINA18DecimalDigits A ) ` i
        )
        ^
        ( VERINA18CountDigits A )
      )
  ) $.
$}

verina18-precondition-definition $a |- (
  VERINA18Pre A
) <-> (
  A e. NN0
) $.

verina18-is-armstrong-definition $a |- (
  VERINA18IsArmstrong A
) = if (
  (
    VERINA18SumPowers
      A
      ( VERINA18CountDigits A )
  ) = A ,
  1 ,
  0
) $.

verina18-postcondition-definition $a |- (
  VERINA18Post A B
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
      A = ( VERINA18DigitPowerSum A )
    )
    /\
    (
      B = 0
      ->
      A =/= ( VERINA18DigitPowerSum A )
    )
  )
) $.

verina-advanced-18-is-armstrong $a |- A. n e. NN0
  (
    ( VERINA18Pre n )
    ->
    (
      VERINA18Post
        n
        ( VERINA18IsArmstrong n )
    )
  )
$.
