$(
  Statement-only formalization of Thousand Theorems corpus artifact Q420714
  (thousand-theorems__metamath__Q420714), "Akra-Bazzi theorem": every
  real-valued recurrence over an arbitrary finite nonempty family, with
  positive coefficients, contraction factors strictly between zero and one,
  a nonnegative polynomially growing toll function, and lower-order rounding
  perturbations, is eventually bounded in norm by a constant multiple of its
  Akra-Bazzi asymptotic bound. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q420714Rpow is real exponentiation on the nonnegative bases used below,
  including Mathlib's values at zero. Q420714Exponent is the unique real p
  satisfying sum_i a_i b_i^p = 1. Q420714Asymp expands the source definition
  n^p + n^p sum_{u < n} g(u) / u^(p+1). The quotient is explicitly zero when
  its denominator is zero, matching Lean's total division.

  Q420714GrowsPolynomially, Q420714SmallError, and Q420714Recurrence expand
  every field of the Lean AkraBazziRecurrence structure. Q420714BigO is the
  norm inequality definition of Big-O along the natural-number atTop filter.
  The final $a assertion is the translated corpus statement. All $a
  declarations here are unproved syntax, definitions, or the final statement;
  this file has no $p proof.
$)

$c
  Q420714Rpow
  Q420714Exponent
  Q420714Asymp
  Q420714GrowsPolynomially
  Q420714SmallError
  Q420714Recurrence
  Q420714BigO
$.

q420714-rpow-syntax $a class ( Q420714Rpow x y ) $.
q420714-exponent-syntax $a class ( Q420714Exponent I A B ) $.
q420714-asymp-syntax $a class ( Q420714Asymp I G A B n ) $.
q420714-grows-syntax $a wff ( Q420714GrowsPolynomially G ) $.
q420714-small-error-syntax $a wff ( Q420714SmallError I B R ) $.
q420714-recurrence-syntax $a wff ( Q420714Recurrence I T G A B R ) $.
q420714-big-o-syntax $a wff ( Q420714BigO T H ) $.

${
  $d x y $.

  q420714-rpow-definition $a |- (
    Q420714Rpow x y
  ) = if (
    x = 0
    ,
    if ( y = 0 , 1 , 0 )
    ,
    ( exp ` ( ( log ` x ) x. y ) )
  ) $.
$}

${
  $d I A B i p $.

  q420714-exponent-definition $a |- (
    Q420714Exponent I A B
  ) = (
    iota_ p e. RR
      (
        sum_ i e. I
          ( ( A ` i ) x. ( Q420714Rpow ( B ` i ) p ) )
      )
      =
      1
  ) $.
$}

${
  $d I G A B n p u $.

  q420714-asymp-definition $a |- (
    Q420714Asymp I G A B n
  ) = (
    ( Q420714Rpow n ( Q420714Exponent I A B ) )
    +
    (
      ( Q420714Rpow n ( Q420714Exponent I A B ) )
      x.
      sum_ u e. ( 0 ..^ n )
        if (
          (
            Q420714Rpow
              u
              ( ( Q420714Exponent I A B ) + 1 )
          )
          =
          0
          ,
          0
          ,
          (
            ( G ` u )
            /
            (
              Q420714Rpow
                u
                ( ( Q420714Exponent I A B ) + 1 )
            )
          )
        )
    )
  ) $.
$}

${
  $d G b c d m u x $.

  q420714-grows-definition $a |- (
    ( Q420714GrowsPolynomially G )
    <->
    A. b e. RR
      (
        ( 0 < b /\ b < 1 )
        ->
        E. c e. RR+
          E. d e. RR+
            E. m e. RR
              A. x e. RR
                (
                  m <_ x
                  ->
                  A. u e. RR
                    (
                      (
                        ( b x. x ) <_ u
                        /\
                        u <_ x
                      )
                      ->
                      (
                        ( c x. ( G ` x ) ) <_ ( G ` u )
                        /\
                        ( G ` u ) <_ ( d x. ( G ` x ) )
                      )
                    )
                )
      )
  ) $.
$}

${
  $d I B R e i m n $.

  q420714-small-error-definition $a |- (
    ( Q420714SmallError I B R )
    <->
    A. i e. I
      A. e e. RR+
        E. m e. NN0
          A. n e. ( ZZ>= ` m )
            (
              abs
              `
              (
                ( ( R ` i ) ` n )
                -
                ( ( B ` i ) x. n )
              )
            )
            <_
            (
              e
              x.
              (
                abs
                `
                (
                  n
                  /
                  ( ( log ` n ) ^ 2 )
                )
              )
            )
  ) $.
$}

${
  $d I T G A B R i m n x $.

  q420714-recurrence-definition $a |- (
    ( Q420714Recurrence I T G A B R )
    <->
    E. m e. NN0
      (
        0 < m
        /\
        A. i e. I
          (
            0 < ( A ` i )
            /\
            0 < ( B ` i )
            /\
            ( B ` i ) < 1
          )
        /\
        A. x e. ( 0 [,) +oo )
          0 <_ ( G ` x )
        /\
        ( Q420714GrowsPolynomially G )
        /\
        A. n e. ( ZZ>= ` m )
          (
            ( T ` n )
            =
            (
              sum_ i e. I
                (
                  ( A ` i )
                  x.
                  ( T ` ( ( R ` i ) ` n ) )
                )
              +
              ( G ` n )
            )
          )
        /\
        A. n e. NN0
          (
            n < m
            ->
            0 < ( T ` n )
          )
        /\
        A. i e. I
          A. n e. ( ZZ>= ` m )
            ( ( R ` i ) ` n ) < n
        /\
        ( Q420714SmallError I B R )
      )
  ) $.
$}

${
  $d T H c m n $.

  q420714-big-o-definition $a |- (
    ( Q420714BigO T H )
    <->
    E. c e. ( 0 [,) +oo )
      E. m e. NN0
        A. n e. ( ZZ>= ` m )
          (
            ( abs ` ( T ` n ) )
            <_
            ( c x. ( abs ` ( H ` n ) ) )
          )
  ) $.
$}

${
  $d I T G A B R n $.

  thousand-theorems-q420714-akra-bazzi-upper-bound $a |-
    A. I e. Fin
      A. T e. ( RR ^m NN0 )
        A. G e. ( RR ^m RR )
          A. A e. ( RR ^m I )
            A. B e. ( RR ^m I )
              A. R e. ( ( NN0 ^m NN0 ) ^m I )
                (
                  (
                    I =/= (/)
                    /\
                    ( Q420714Recurrence I T G A B R )
                  )
                  ->
                  (
                    Q420714BigO
                      T
                      ( n e. NN0 |-> ( Q420714Asymp I G A B n ) )
                  )
                )
  $.
$}
