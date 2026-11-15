$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_67 (verina__metamath__verina_advanced_67), catalog title
  runLengthEncode: the exact accumulator-recursive Unicode-string program
  groups consecutive equal characters into positive run lengths with distinct
  adjacent run characters and decoding equal to the input. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  VERINA67Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINA67Char represents arbitrary Lean strings extensionally through
  String.data. VERINA67Run is Char x Nat, so Word VERINA67Run is exactly the
  result type List (Char x Nat).

  VERINA67EncodeStepGraph gives one exact source encodeAux update on its
  reversed accumulator. An empty accumulator becomes the singleton current
  run. Otherwise an equal current character increments only the head count,
  while a different character is prepended with count one.
  VERINA67EncodeAuxGraph records the complete deterministic accumulator trace
  for arbitrary typed accumulator and remaining-input arguments, then applies
  exact list reversal at exhaustion. VERINA67EncodeAux selects its unique
  result, and VERINA67RunLengthEncode calls it with the empty accumulator and
  String.data. Thus the implementation is fixed independently of the
  postcondition and permits no extra outputs.

  VERINA67DecodeGraph records the exact decodeRLE recursion by cumulative run
  offsets: each run contributes precisely its count copies of its character,
  in list order. VERINA67DecodeRLE selects that unique decoded string.
  VERINA67NatSub is Lean's truncated natural subtraction and is used to retain
  the source adjacent-index bound result.length - 1 exactly.

  VERINA67Pre is the source True precondition on typed String inputs.
  VERINA67Post preserves all three source conjuncts: every run count is
  positive, every adjacent pair has distinct characters, and decodeRLE of the
  result equals the input. The proof-valued precondition argument is
  computationally and propositionally unused and is represented by the
  explicit antecedent of the final correctness assertion. Every earlier $a is
  syntax or a faithful definition, and this root statement file introduces no
  $p declaration.
$)

$c
  VERINA67Char VERINA67Run
  VERINA67NatSub
  VERINA67ReverseGraph VERINA67Reverse
  VERINA67EncodeStepGraph
  VERINA67EncodeAuxGraph VERINA67EncodeAux
  VERINA67RunLengthEncode
  VERINA67DecodeGraph VERINA67DecodeRLE
  VERINA67Pre VERINA67Post
$.

verina67-char-syntax
  $a class VERINA67Char $.
verina67-run-syntax
  $a class VERINA67Run $.
verina67-nat-sub-syntax
  $a class ( VERINA67NatSub A B ) $.
verina67-reverse-graph-syntax
  $a wff ( VERINA67ReverseGraph A B ) $.
verina67-reverse-syntax
  $a class ( VERINA67Reverse A ) $.
verina67-encode-step-graph-syntax
  $a wff ( VERINA67EncodeStepGraph A B C ) $.
verina67-encode-aux-graph-syntax
  $a wff ( VERINA67EncodeAuxGraph A B C ) $.
verina67-encode-aux-syntax
  $a class ( VERINA67EncodeAux A B ) $.
verina67-program-syntax
  $a class ( VERINA67RunLengthEncode A ) $.
verina67-decode-graph-syntax
  $a wff ( VERINA67DecodeGraph A B ) $.
verina67-decode-rle-syntax
  $a class ( VERINA67DecodeRLE A ) $.
verina67-precondition-syntax
  $a wff ( VERINA67Pre A ) $.
verina67-postcondition-syntax
  $a wff ( VERINA67Post A B ) $.

verina67-char-definition $a |- VERINA67Char =
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

verina67-run-definition $a |- VERINA67Run = (
  VERINA67Char X. NN0
) $.

verina67-nat-sub-definition $a |- (
  VERINA67NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d i A B $.

  verina67-reverse-graph-definition $a |- (
    VERINA67ReverseGraph A B
  ) <-> (
    (
      A e. Word VERINA67Run
      /\
      B e. Word VERINA67Run
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

  verina67-reverse-definition $a |- (
    VERINA67Reverse A
  ) = (
    iota_ y e. Word VERINA67Run
      ( VERINA67ReverseGraph A y )
  ) $.
$}

${
  $d j A B C $.

  verina67-encode-step-graph-definition $a |- (
    VERINA67EncodeStepGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA67Run
        /\
        B e. VERINA67Char
      )
      /\
      C e. Word VERINA67Run
    )
    /\
    (
      (
        A = (/)
        /\
        (
          ( # ` C ) = 1
          /\
          ( C ` 0 ) = <. B , 1 >.
        )
      )
      \/
      (
        A =/= (/)
        /\
        (
          (
            ( 1st ` ( A ` 0 ) ) = B
            /\
            (
              ( # ` C ) = ( # ` A )
              /\
              (
                ( C ` 0 ) = <.
                  B ,
                  ( ( 2nd ` ( A ` 0 ) ) + 1 )
                >.
                /\
                A. j e. ( 1 ..^ ( # ` A ) )
                  ( C ` j ) = ( A ` j )
              )
            )
          )
          \/
          (
            ( 1st ` ( A ` 0 ) ) =/= B
            /\
            (
              ( # ` C ) = ( ( # ` A ) + 1 )
              /\
              (
                ( C ` 0 ) = <. B , 1 >.
                /\
                A. j e. ( 0 ..^ ( # ` A ) )
                  ( C ` ( j + 1 ) ) = ( A ` j )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d i t A B C $.

  verina67-encode-aux-graph-definition $a |- (
    VERINA67EncodeAuxGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA67Run
        /\
        B e. Word VERINA67Char
      )
      /\
      C e. Word VERINA67Run
    )
    /\
    E. t e. Word ( Word VERINA67Run )
      (
        (
          ( # ` t ) = ( ( # ` B ) + 1 )
          /\
          ( t ` 0 ) = A
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` B ) )
            (
              VERINA67EncodeStepGraph
                ( t ` i )
                ( B ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          C = (
            VERINA67Reverse
              ( t ` ( # ` B ) )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina67-encode-aux-definition $a |- (
    VERINA67EncodeAux A B
  ) = (
    iota_ y e. Word VERINA67Run
      ( VERINA67EncodeAuxGraph A B y )
  ) $.
$}

verina67-program-definition $a |- (
  VERINA67RunLengthEncode A
) = (
  VERINA67EncodeAux
    (/)
    A
) $.

${
  $d i k p A B $.

  verina67-decode-graph-definition $a |- (
    VERINA67DecodeGraph A B
  ) <-> (
    (
      A e. Word VERINA67Run
      /\
      B e. Word VERINA67Char
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

  verina67-decode-rle-definition $a |- (
    VERINA67DecodeRLE A
  ) = (
    iota_ y e. Word VERINA67Char
      ( VERINA67DecodeGraph A y )
  ) $.
$}

verina67-precondition-definition $a |- (
  VERINA67Pre A
) <-> (
  A e. Word VERINA67Char
) $.

${
  $d i A B $.

  verina67-postcondition-definition $a |- (
    VERINA67Post A B
  ) <-> (
    (
      A e. Word VERINA67Char
      /\
      B e. Word VERINA67Run
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` B ) )
        0 < ( 2nd ` ( B ` i ) )
      /\
      (
        A. i e. NN0
          (
            i < (
              VERINA67NatSub
                ( # ` B )
                1
            )
            ->
            (
              1st ` ( B ` i )
            ) =/= (
              1st ` ( B ` ( i + 1 ) )
            )
          )
        /\
        ( VERINA67DecodeRLE B ) = A
      )
    )
  ) $.
$}

verina-advanced-67-run-length-encode $a |-
  A. s e. Word VERINA67Char
    (
      ( VERINA67Pre s )
      ->
      (
        VERINA67Post
          s
          ( VERINA67RunLengthEncode s )
      )
    )
$.
