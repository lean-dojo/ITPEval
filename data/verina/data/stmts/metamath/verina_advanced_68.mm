$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_68 (verina__metamath__verina_advanced_68), catalog title
  runLengthEncoder: the exact Unicode-string run-length encoder serializes
  each maximal run as its character followed by its positive decimal count,
  with the source parser, format, reconstruction, and emptiness correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA68Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINA68Char represents arbitrary Lean strings extensionally through
  String.data. VERINA68IsDigit is the source ASCII Char.isDigit test.
  VERINA68Chars and VERINA68StringMk are the source conversions and are
  extensionally identity maps on this representation. VERINA68CharEq is the
  source Boolean character equality.

  VERINA68Digits is the source local decimal recursion, characterized by its
  unique canonical most-significant-first base-ten digit word, including one
  zero digit for zero. VERINA68NumToString adds the ASCII zero code to every
  digit, exactly reproducing Char.ofNat and String.mk in numToString.

  VERINA68EncodeStepGraph records one exact update of the source encode
  recursion while accumulating already-flushed output on the right. None
  selects the first input character with count one; an equal character
  increments the count; and a different character flushes the old character
  and its decimal count before starting a new run. VERINA68EncodeGraph records
  the complete deterministic trace and performs the source exhaustion flush.
  VERINA68RunLengthEncoder preserves the explicit empty-input branch and,
  otherwise, invokes encode on tail, head?, and count one. Thus its output is
  fixed independently of the postcondition and the trace permits no extra
  outputs.

  VERINA68ParseStepGraph is the exact parseState transition. Its absorbing
  invalid state represents the source immediate [] result for a digit without
  a preceding character; decimal counts and the reversed accumulator follow
  the source branches exactly. VERINA68ParseEncodedString performs the final
  optional-pair insertion and reversal. VERINA68FormatValid uses the exact
  checkPairs control flow, including its nowDigit flag and one- versus
  two-character recursive advances. VERINA68Expanded is the exact flatMap of
  List.replicate over parsed pairs.

  VERINA68Pre requires a typed input string whose characters are all
  non-digits. VERINA68Post is precisely the conjunction of formatValid,
  reconstructed-content equality, and equality of input/output emptiness.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent of the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINA68Char VERINA68IsDigit VERINA68CharEq
  VERINA68Chars VERINA68StringMk
  VERINA68None VERINA68Some
  VERINA68OptionChar VERINA68OptionNat VERINA68Run
  VERINA68CountDigitsGraph VERINA68CountDigits
  VERINA68DigitsGraph VERINA68Digits
  VERINA68NumToStringGraph VERINA68NumToString
  VERINA68AppendGraph VERINA68Append
  VERINA68CharSingletonGraph VERINA68CharSingleton
  VERINA68RunSingletonGraph VERINA68RunSingleton VERINA68ConsRun
  VERINA68GetOption VERINA68TailGraph VERINA68Tail
  VERINA68EncodeState VERINA68EncodeStepGraph
  VERINA68EncodeFinish VERINA68EncodeGraph VERINA68Encode
  VERINA68RunLengthEncoder
  VERINA68ReverseRunGraph VERINA68ReverseRun
  VERINA68ParseState VERINA68ParseInvalid
  VERINA68ParseStepGraph VERINA68ParseFinish
  VERINA68ParseEncodedGraph VERINA68ParseEncodedString
  VERINA68FormatState VERINA68FormatContinue
  VERINA68FormatStop VERINA68FormatGraph VERINA68FormatValid
  VERINA68ExpandGraph VERINA68Expanded
  VERINA68ContentValid VERINA68NonEmptyValid
  VERINA68Pre VERINA68Post
$.

verina68-char-syntax
  $a class VERINA68Char $.
verina68-is-digit-syntax
  $a class ( VERINA68IsDigit A ) $.
verina68-char-eq-syntax
  $a class ( VERINA68CharEq A B ) $.
verina68-chars-syntax
  $a class ( VERINA68Chars A ) $.
verina68-string-mk-syntax
  $a class ( VERINA68StringMk A ) $.
verina68-none-syntax
  $a class VERINA68None $.
verina68-some-syntax
  $a class ( VERINA68Some A ) $.
verina68-option-char-syntax
  $a class VERINA68OptionChar $.
verina68-option-nat-syntax
  $a class VERINA68OptionNat $.
verina68-run-syntax
  $a class VERINA68Run $.
verina68-count-digits-graph-syntax
  $a wff ( VERINA68CountDigitsGraph A B ) $.
verina68-count-digits-syntax
  $a class ( VERINA68CountDigits A ) $.
verina68-digits-graph-syntax
  $a wff ( VERINA68DigitsGraph A B ) $.
verina68-digits-syntax
  $a class ( VERINA68Digits A ) $.
verina68-num-to-string-graph-syntax
  $a wff ( VERINA68NumToStringGraph A B ) $.
verina68-num-to-string-syntax
  $a class ( VERINA68NumToString A ) $.
verina68-append-graph-syntax
  $a wff ( VERINA68AppendGraph A B C ) $.
verina68-append-syntax
  $a class ( VERINA68Append A B ) $.
verina68-char-singleton-graph-syntax
  $a wff ( VERINA68CharSingletonGraph A B ) $.
verina68-char-singleton-syntax
  $a class ( VERINA68CharSingleton A ) $.
verina68-run-singleton-graph-syntax
  $a wff ( VERINA68RunSingletonGraph A B ) $.
verina68-run-singleton-syntax
  $a class ( VERINA68RunSingleton A ) $.
verina68-cons-run-syntax
  $a class ( VERINA68ConsRun A B ) $.
verina68-get-option-syntax
  $a class ( VERINA68GetOption A B ) $.
verina68-tail-graph-syntax
  $a wff ( VERINA68TailGraph A B ) $.
verina68-tail-syntax
  $a class ( VERINA68Tail A ) $.
verina68-encode-state-syntax
  $a class VERINA68EncodeState $.
verina68-encode-step-graph-syntax
  $a wff ( VERINA68EncodeStepGraph A B C ) $.
verina68-encode-finish-syntax
  $a class ( VERINA68EncodeFinish A ) $.
verina68-encode-graph-syntax
  $a wff ( VERINA68EncodeGraph A B C D ) $.
verina68-encode-syntax
  $a class ( VERINA68Encode A B C ) $.
verina68-program-syntax
  $a class ( VERINA68RunLengthEncoder A ) $.
verina68-reverse-run-graph-syntax
  $a wff ( VERINA68ReverseRunGraph A B ) $.
verina68-reverse-run-syntax
  $a class ( VERINA68ReverseRun A ) $.
verina68-parse-state-syntax
  $a class VERINA68ParseState $.
verina68-parse-invalid-syntax
  $a class VERINA68ParseInvalid $.
verina68-parse-step-graph-syntax
  $a wff ( VERINA68ParseStepGraph A B C ) $.
verina68-parse-finish-syntax
  $a class ( VERINA68ParseFinish A ) $.
verina68-parse-encoded-graph-syntax
  $a wff ( VERINA68ParseEncodedGraph A B ) $.
verina68-parse-encoded-string-syntax
  $a class ( VERINA68ParseEncodedString A ) $.
verina68-format-state-syntax
  $a class VERINA68FormatState $.
verina68-format-continue-syntax
  $a wff ( VERINA68FormatContinue A B C ) $.
verina68-format-stop-syntax
  $a wff ( VERINA68FormatStop A B C ) $.
verina68-format-graph-syntax
  $a wff ( VERINA68FormatGraph A B ) $.
verina68-format-valid-syntax
  $a class ( VERINA68FormatValid A ) $.
verina68-expand-graph-syntax
  $a wff ( VERINA68ExpandGraph A B ) $.
verina68-expanded-syntax
  $a class ( VERINA68Expanded A ) $.
verina68-content-valid-syntax
  $a class ( VERINA68ContentValid A B ) $.
verina68-nonempty-valid-syntax
  $a class ( VERINA68NonEmptyValid A B ) $.
verina68-precondition-syntax
  $a wff ( VERINA68Pre A ) $.
verina68-postcondition-syntax
  $a wff ( VERINA68Post A B ) $.

verina68-char-definition $a |- VERINA68Char =
  { x e. NN0 |
    (
      x < ; ; ; ; ; ; 1 1 1 4 1 1 2
      /\
      (
        x < ; ; ; ; 5 5 2 9 6
        \/
        ; ; ; ; 5 7 3 4 3 < x
      )
    )
  } $.

verina68-is-digit-definition $a |- (
  VERINA68IsDigit A
) = if (
  (
    ; 4 8 <_ A
    /\
    A <_ ; 5 7
  ) ,
  1 ,
  0
) $.

verina68-char-eq-definition $a |- (
  VERINA68CharEq A B
) = if (
  A = B ,
  1 ,
  0
) $.

verina68-chars-definition $a |- (
  VERINA68Chars A
) = A $.

verina68-string-mk-definition $a |- (
  VERINA68StringMk A
) = A $.

verina68-none-definition $a |- VERINA68None = (/) $.

verina68-some-definition $a |- (
  VERINA68Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina68-option-char-definition $a |- VERINA68OptionChar =
    { x |
      (
        x = VERINA68None
        \/
        E. y e. VERINA68Char
          x = ( VERINA68Some y )
      )
    } $.
$}

${
  $d x y $.

  verina68-option-nat-definition $a |- VERINA68OptionNat =
    { x |
      (
        x = VERINA68None
        \/
        E. y e. NN0
          x = ( VERINA68Some y )
      )
    } $.
$}

verina68-run-definition $a |- VERINA68Run = (
  VERINA68Char X. NN0
) $.

${
  $d i k s A B $.

  verina68-count-digits-graph-definition $a |- (
    VERINA68CountDigitsGraph A B
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

  verina68-count-digits-definition $a |- (
    VERINA68CountDigits A
  ) = (
    iota_ y e. NN0
      ( VERINA68CountDigitsGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina68-digits-graph-definition $a |- (
    VERINA68DigitsGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. Word NN0
    )
    /\
    (
      ( # ` B ) = ( VERINA68CountDigits A )
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

  verina68-digits-definition $a |- (
    VERINA68Digits A
  ) = (
    iota_ y e. Word NN0
      ( VERINA68DigitsGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina68-num-to-string-graph-definition $a |- (
    VERINA68NumToStringGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. Word VERINA68Char
    )
    /\
    (
      ( # ` B ) = ( # ` ( VERINA68Digits A ) )
      /\
      A. i e. ( 0 ..^ ( # ` B ) )
        (
          B ` i
        ) = (
          ( ( VERINA68Digits A ) ` i ) + ; 4 8
        )
    )
  ) $.
$}

${
  $d y A $.

  verina68-num-to-string-definition $a |- (
    VERINA68NumToString A
  ) = (
    iota_ y e. Word VERINA68Char
      ( VERINA68NumToStringGraph A y )
  ) $.
$}

${
  $d i j A B C $.

  verina68-append-graph-definition $a |- (
    VERINA68AppendGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA68Char
        /\
        B e. Word VERINA68Char
      )
      /\
      C e. Word VERINA68Char
    )
    /\
    (
      ( # ` C ) = ( ( # ` A ) + ( # ` B ) )
      /\
      (
        A. i e. ( 0 ..^ ( # ` A ) )
          ( C ` i ) = ( A ` i )
        /\
        A. j e. ( 0 ..^ ( # ` B ) )
          ( C ` ( ( # ` A ) + j ) ) = ( B ` j )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina68-append-definition $a |- (
    VERINA68Append A B
  ) = (
    iota_ y e. Word VERINA68Char
      ( VERINA68AppendGraph A B y )
  ) $.
$}

verina68-char-singleton-graph-definition $a |- (
  VERINA68CharSingletonGraph A B
) <-> (
  (
    A e. VERINA68Char
    /\
    B e. Word VERINA68Char
  )
  /\
  (
    ( # ` B ) = 1
    /\
    ( B ` 0 ) = A
  )
) $.

${
  $d y A $.

  verina68-char-singleton-definition $a |- (
    VERINA68CharSingleton A
  ) = (
    iota_ y e. Word VERINA68Char
      ( VERINA68CharSingletonGraph A y )
  ) $.
$}

verina68-run-singleton-graph-definition $a |- (
  VERINA68RunSingletonGraph A B
) <-> (
  (
    A e. VERINA68Run
    /\
    B e. Word VERINA68Run
  )
  /\
  (
    ( # ` B ) = 1
    /\
    ( B ` 0 ) = A
  )
) $.

${
  $d y A $.

  verina68-run-singleton-definition $a |- (
    VERINA68RunSingleton A
  ) = (
    iota_ y e. Word VERINA68Run
      ( VERINA68RunSingletonGraph A y )
  ) $.
$}

${
  $d i y A B $.

  verina68-cons-run-definition $a |- (
    VERINA68ConsRun A B
  ) = (
    iota_ y e. Word VERINA68Run
      (
        (
          A e. VERINA68Run
          /\
          B e. Word VERINA68Run
        )
        /\
        (
          (
            ( # ` y ) = ( ( # ` B ) + 1 )
            /\
            ( y ` 0 ) = A
          )
          /\
          A. i e. ( 0 ..^ ( # ` B ) )
            ( y ` ( i + 1 ) ) = ( B ` i )
        )
      )
  ) $.
$}

verina68-get-option-definition $a |- (
  VERINA68GetOption A B
) = if (
  B < ( # ` A ) ,
  ( VERINA68Some ( A ` B ) ) ,
  VERINA68None
) $.

${
  $d i A B $.

  verina68-tail-graph-definition $a |- (
    VERINA68TailGraph A B
  ) <-> (
    (
      A e. Word VERINA68Char
      /\
      B e. Word VERINA68Char
    )
    /\
    (
      ( # ` B ) = if (
        ( # ` A ) = 0 ,
        0 ,
        ( ( # ` A ) - 1 )
      )
      /\
      A. i e. ( 0 ..^ ( # ` B ) )
        ( B ` i ) = ( A ` ( i + 1 ) )
    )
  ) $.
$}

${
  $d y A $.

  verina68-tail-definition $a |- (
    VERINA68Tail A
  ) = (
    iota_ y e. Word VERINA68Char
      ( VERINA68TailGraph A y )
  ) $.
$}

verina68-encode-state-definition $a |- VERINA68EncodeState = (
  VERINA68OptionChar X. ( NN0 X. Word VERINA68Char )
) $.

verina68-encode-step-graph-definition $a |- (
  VERINA68EncodeStepGraph A B C
) <-> (
  (
    (
      A e. VERINA68EncodeState
      /\
      B e. VERINA68Char
    )
    /\
    C e. VERINA68EncodeState
  )
  /\
  (
    (
      ( 1st ` A ) = VERINA68None
      /\
      C = <.
        ( VERINA68Some B ) ,
        <. 1 , ( 2nd ` ( 2nd ` A ) ) >.
      >.
    )
    \/
    (
      (
        ( 1st ` A ) =/= VERINA68None
        /\
        (
          VERINA68CharEq
            B
            ( 2nd ` ( 1st ` A ) )
        ) = 1
      )
      /\
      C = <.
        ( 1st ` A ) ,
        <.
          ( ( 1st ` ( 2nd ` A ) ) + 1 ) ,
          ( 2nd ` ( 2nd ` A ) )
        >.
      >.
    )
    \/
    (
      (
        ( 1st ` A ) =/= VERINA68None
        /\
        (
          VERINA68CharEq
            B
            ( 2nd ` ( 1st ` A ) )
        ) = 0
      )
      /\
      C = <.
        ( VERINA68Some B ) ,
        <.
          1 ,
          (
            VERINA68Append
              (
                VERINA68Append
                  ( 2nd ` ( 2nd ` A ) )
                  (
                    VERINA68CharSingleton
                      ( 2nd ` ( 1st ` A ) )
                  )
              )
              (
                VERINA68NumToString
                  ( 1st ` ( 2nd ` A ) )
              )
          )
        >.
      >.
    )
  )
) $.

verina68-encode-finish-definition $a |- (
  VERINA68EncodeFinish A
) = if (
  ( 1st ` A ) = VERINA68None ,
  ( 2nd ` ( 2nd ` A ) ) ,
  (
    VERINA68Append
      (
        VERINA68Append
          ( 2nd ` ( 2nd ` A ) )
          (
            VERINA68CharSingleton
              ( 2nd ` ( 1st ` A ) )
          )
      )
      (
        VERINA68NumToString
          ( 1st ` ( 2nd ` A ) )
      )
  )
) $.

${
  $d i t A B C D $.

  verina68-encode-graph-definition $a |- (
    VERINA68EncodeGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word VERINA68Char
          /\
          B e. VERINA68OptionChar
        )
        /\
        C e. NN0
      )
      /\
      D e. Word VERINA68Char
    )
    /\
    E. t e. Word VERINA68EncodeState
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = <. B , <. C , (/) >. >.
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              VERINA68EncodeStepGraph
                ( t ` i )
                ( A ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          D = (
            VERINA68EncodeFinish
              ( t ` ( # ` A ) )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verina68-encode-definition $a |- (
    VERINA68Encode A B C
  ) = (
    iota_ y e. Word VERINA68Char
      ( VERINA68EncodeGraph A B C y )
  ) $.
$}

verina68-program-definition $a |- (
  VERINA68RunLengthEncoder A
) = if (
  ( # ` A ) = 0 ,
  (/) ,
  (
    VERINA68Encode
      ( VERINA68Tail ( VERINA68Chars A ) )
      ( VERINA68GetOption ( VERINA68Chars A ) 0 )
      1
  )
) $.

${
  $d i A B $.

  verina68-reverse-run-graph-definition $a |- (
    VERINA68ReverseRunGraph A B
  ) <-> (
    (
      A e. Word VERINA68Run
      /\
      B e. Word VERINA68Run
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = (
          A ` ( ( ( # ` A ) - 1 ) - i )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina68-reverse-run-definition $a |- (
    VERINA68ReverseRun A
  ) = (
    iota_ y e. Word VERINA68Run
      ( VERINA68ReverseRunGraph A y )
  ) $.
$}

verina68-parse-state-definition $a |- VERINA68ParseState = (
  { 0 , 1 } X.
  (
    VERINA68OptionChar X.
    ( VERINA68OptionNat X. Word VERINA68Run )
  )
) $.

verina68-parse-invalid-definition $a |- VERINA68ParseInvalid = <.
  0 ,
  <. VERINA68None , <. VERINA68None , (/) >. >.
>. $.

verina68-parse-step-graph-definition $a |- (
  VERINA68ParseStepGraph A B C
) <-> (
  (
    (
      A e. VERINA68ParseState
      /\
      B e. VERINA68Char
    )
    /\
    C e. VERINA68ParseState
  )
  /\
  (
    (
      ( 1st ` A ) = 0
      /\
      C = A
    )
    \/
    (
      (
        (
          ( 1st ` A ) = 1
          /\
          ( VERINA68IsDigit B ) = 1
        )
        /\
        (
          1st ` ( 2nd ` A )
        ) = VERINA68None
      )
      /\
      C = VERINA68ParseInvalid
    )
    \/
    (
      (
        (
          ( 1st ` A ) = 1
          /\
          ( VERINA68IsDigit B ) = 1
        )
        /\
        (
          1st ` ( 2nd ` A )
        ) =/= VERINA68None
      )
      /\
      C = <.
        1 ,
        <.
          ( 1st ` ( 2nd ` A ) ) ,
          <.
            (
              VERINA68Some
                if (
                  (
                    1st ` ( 2nd ` ( 2nd ` A ) )
                  ) = VERINA68None ,
                  ( B - ; 4 8 ) ,
                  (
                    (
                      (
                        2nd `
                          ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
                      ) x. ; 1 0
                    )
                    +
                    ( B - ; 4 8 )
                  )
                )
            ) ,
            ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
          >.
        >.
      >.
    )
    \/
    (
      (
        ( 1st ` A ) = 1
        /\
        ( VERINA68IsDigit B ) = 0
      )
      /\
      C = <.
        1 ,
        <.
          ( VERINA68Some B ) ,
          <.
            VERINA68None ,
            if (
              (
                (
                  1st ` ( 2nd ` A )
                ) =/= VERINA68None
                /\
                (
                  1st ` ( 2nd ` ( 2nd ` A ) )
                ) =/= VERINA68None
              ) ,
              (
                VERINA68ConsRun
                  <.
                    (
                      2nd ` ( 1st ` ( 2nd ` A ) )
                    ) ,
                    (
                      2nd `
                        ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
                    )
                  >.
                  ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
              ) ,
              ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
            )
          >.
        >.
      >.
    )
  )
) $.

verina68-parse-finish-definition $a |- (
  VERINA68ParseFinish A
) = if (
  ( 1st ` A ) = 0 ,
  (/) ,
  (
    VERINA68ReverseRun
      if (
        (
          (
            1st ` ( 2nd ` A )
          ) =/= VERINA68None
          /\
          (
            1st ` ( 2nd ` ( 2nd ` A ) )
          ) =/= VERINA68None
        ) ,
        (
          VERINA68ConsRun
            <.
              ( 2nd ` ( 1st ` ( 2nd ` A ) ) ) ,
              (
                2nd `
                  ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
              )
            >.
            ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
        ) ,
        ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
      )
  )
) $.

${
  $d i t A B $.

  verina68-parse-encoded-graph-definition $a |- (
    VERINA68ParseEncodedGraph A B
  ) <-> (
    (
      A e. Word VERINA68Char
      /\
      B e. Word VERINA68Run
    )
    /\
    E. t e. Word VERINA68ParseState
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = <.
            1 ,
            <. VERINA68None , <. VERINA68None , (/) >. >.
          >.
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              VERINA68ParseStepGraph
                ( t ` i )
                ( A ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          B = (
            VERINA68ParseFinish
              ( t ` ( # ` A ) )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina68-parse-encoded-string-definition $a |- (
    VERINA68ParseEncodedString A
  ) = (
    iota_ y e. Word VERINA68Run
      ( VERINA68ParseEncodedGraph A y )
  ) $.
$}

verina68-format-state-definition $a |- VERINA68FormatState = (
  NN0 X. { 0 , 1 }
) $.

verina68-format-continue-definition $a |- (
  VERINA68FormatContinue A B C
) <-> (
  (
    (
      A e. Word VERINA68Char
      /\
      B e. VERINA68FormatState
    )
    /\
    C e. VERINA68FormatState
  )
  /\
  (
    (
      (
        ( 1st ` B ) < ( # ` A )
        /\
        (
          (
            ( 2nd ` B ) = 1
            /\
            (
              VERINA68IsDigit
                ( A ` ( 1st ` B ) )
            ) = 1
          )
          /\
          C = <. ( ( 1st ` B ) + 1 ) , 1 >.
        )
      )
    )
    \/
    (
      (
        (
          ( 1st ` B ) < ( # ` A )
          /\
          -.
            (
              ( 2nd ` B ) = 1
              /\
              (
                VERINA68IsDigit
                  ( A ` ( 1st ` B ) )
              ) = 1
            )
        )
        /\
        (
          ( ( 1st ` B ) + 1 ) < ( # ` A )
          /\
          (
            VERINA68IsDigit
              ( A ` ( ( 1st ` B ) + 1 ) )
          ) = 1
        )
      )
      /\
      C = <. ( ( 1st ` B ) + 2 ) , 1 >.
    )
  )
) $.

verina68-format-stop-definition $a |- (
  VERINA68FormatStop A B C
) <-> (
  (
    (
      A e. Word VERINA68Char
      /\
      B e. VERINA68FormatState
    )
    /\
    C e. { 0 , 1 }
  )
  /\
  (
    (
      ( 1st ` B ) = ( # ` A )
      /\
      C = 1
    )
    \/
    (
      (
        (
          ( 1st ` B ) < ( # ` A )
          /\
          -.
            (
              ( 2nd ` B ) = 1
              /\
              (
                VERINA68IsDigit
                  ( A ` ( 1st ` B ) )
              ) = 1
            )
        )
        /\
        (
          ( # ` A ) <_ ( ( 1st ` B ) + 1 )
          \/
          (
            VERINA68IsDigit
              ( A ` ( ( 1st ` B ) + 1 ) )
          ) = 0
        )
      )
      /\
      C = 0
    )
  )
) $.

${
  $d i k t A B $.

  verina68-format-graph-definition $a |- (
    VERINA68FormatGraph A B
  ) <-> (
    (
      A e. Word VERINA68Char
      /\
      B e. { 0 , 1 }
    )
    /\
    E. k e. NN0 E. t e. Word VERINA68FormatState
      (
        (
          ( # ` t ) = ( k + 1 )
          /\
          ( t ` 0 ) = <. 0 , 0 >.
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              VERINA68FormatContinue
                A
                ( t ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          (
            VERINA68FormatStop
              A
              ( t ` k )
              B
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina68-format-valid-definition $a |- (
    VERINA68FormatValid A
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA68FormatGraph A y )
  ) $.
$}

${
  $d i k p A B $.

  verina68-expand-graph-definition $a |- (
    VERINA68ExpandGraph A B
  ) <-> (
    (
      A e. Word VERINA68Run
      /\
      B e. Word VERINA68Char
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( ( # ` A ) + 1 )
          /\
          ( p ` 0 ) = 0
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              p ` ( i + 1 )
            ) = (
              ( p ` i )
              + ( 2nd ` ( A ` i ) )
            )
          /\
          (
            ( # ` B ) = ( p ` ( # ` A ) )
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              A. k e. ( 0 ..^ ( 2nd ` ( A ` i ) ) )
                (
                  B ` ( ( p ` i ) + k )
                ) = (
                  1st ` ( A ` i )
                )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina68-expanded-definition $a |- (
    VERINA68Expanded A
  ) = (
    iota_ y e. Word VERINA68Char
      ( VERINA68ExpandGraph A y )
  ) $.
$}

verina68-content-valid-definition $a |- (
  VERINA68ContentValid A B
) = if (
  (
    VERINA68Expanded
      ( VERINA68ParseEncodedString B )
  ) = (
    VERINA68Chars A
  ) ,
  1 ,
  0
) $.

verina68-nonempty-valid-definition $a |- (
  VERINA68NonEmptyValid A B
) = if (
  (
    (
      ( # ` A ) = 0
      /\
      ( # ` B ) = 0
    )
    \/
    (
      0 < ( # ` A )
      /\
      0 < ( # ` B )
    )
  ) ,
  1 ,
  0
) $.

${
  $d i A $.

  verina68-precondition-definition $a |- (
    VERINA68Pre A
  ) <-> (
    (
      A e. Word VERINA68Char
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( VERINA68IsDigit ( A ` i ) ) = 0
    )
  ) $.
$}

verina68-postcondition-definition $a |- (
  VERINA68Post A B
) <-> (
  (
    A e. Word VERINA68Char
    /\
    B e. Word VERINA68Char
  )
  /\
  (
    (
      VERINA68FormatValid B
    ) = 1
    /\
    (
      (
        VERINA68ContentValid A B
      ) = 1
      /\
      (
        VERINA68NonEmptyValid A B
      ) = 1
    )
  )
) $.

verina-advanced-68-run-length-encoder $a |-
  A. s e. Word VERINA68Char
    (
      ( VERINA68Pre s )
      ->
      (
        VERINA68Post
          s
          ( VERINA68RunLengthEncoder s )
      )
    )
$.
