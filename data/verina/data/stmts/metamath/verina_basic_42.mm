$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_42
  (verina__metamath__verina_basic_42), catalog title countDigits: the exact
  executable filter-length computation counts ASCII digit characters in an
  arbitrary Unicode string and satisfies its two-sided natural-subtraction
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB42Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB42Char represents arbitrary Lean strings extensionally through
  String.toList. For a word w, # ` w is its natural-number length, w ` i is
  zero-based lookup, and 0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB42IsDigit is the source Boolean helper: it returns true exactly for
  character codes from 48 through 57, the inclusive ASCII range '0' through
  '9'. VERINAB42ToCharList is the source String.toList conversion and is
  extensionally the identity on this word representation.

  VERINAB42FilteredLength is the cardinality of exactly those valid indices
  whose characters make VERINAB42IsDigit true. This is definitionally equal
  to List.length (List.filter isDigit s.toList), including on the empty
  string. VERINAB42CountDigits is therefore the exact executable source
  result, fixed independently of the postcondition and admitting no
  additional outputs.

  VERINAB42NatSub is Lean's truncated natural subtraction. VERINAB42Pre is
  the source True precondition on typed String inputs. VERINAB42Post preserves
  both source conjuncts: result minus the filtered length is zero, and the
  filtered length minus result is zero. The proof-valued precondition
  arguments to the implementation and postcondition have no computational or
  propositional effect beyond the explicit antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB42Char VERINAB42IsDigit VERINAB42ToCharList
  VERINAB42FilteredLength VERINAB42NatSub
  VERINAB42Pre VERINAB42CountDigits VERINAB42Post
$.

verinab42-char-syntax
  $a class VERINAB42Char $.
verinab42-is-digit-syntax
  $a class ( VERINAB42IsDigit A ) $.
verinab42-to-char-list-syntax
  $a class ( VERINAB42ToCharList A ) $.
verinab42-filtered-length-syntax
  $a class ( VERINAB42FilteredLength A ) $.
verinab42-nat-sub-syntax
  $a class ( VERINAB42NatSub A B ) $.
verinab42-precondition-syntax
  $a wff ( VERINAB42Pre A ) $.
verinab42-program-syntax
  $a class ( VERINAB42CountDigits A ) $.
verinab42-postcondition-syntax
  $a wff ( VERINAB42Post A B ) $.

verinab42-char-definition $a |- VERINAB42Char =
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

verinab42-is-digit-definition $a |- (
  VERINAB42IsDigit A
) = if (
  (
    ; 4 8 <_ A
    /\
    A <_ ; 5 7
  ) ,
  1 ,
  0
) $.

verinab42-to-char-list-definition $a |- (
  VERINAB42ToCharList A
) = A $.

${
  $d i A $.

  verinab42-filtered-length-definition $a |- (
    VERINAB42FilteredLength A
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( VERINAB42IsDigit ( A ` i ) ) = 1
    }
  ) $.
$}

verinab42-nat-sub-definition $a |- (
  VERINAB42NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab42-precondition-definition $a |- (
  VERINAB42Pre A
) <-> (
  A e. Word VERINAB42Char
) $.

verinab42-program-definition $a |- (
  VERINAB42CountDigits A
) = (
  VERINAB42FilteredLength
    ( VERINAB42ToCharList A )
) $.

verinab42-postcondition-definition $a |- (
  VERINAB42Post A B
) <-> (
  (
    A e. Word VERINAB42Char
    /\
    B e. NN0
  )
  /\
  (
    (
      VERINAB42NatSub
        B
        (
          VERINAB42FilteredLength
            ( VERINAB42ToCharList A )
        )
    ) = 0
    /\
    (
      VERINAB42NatSub
        (
          VERINAB42FilteredLength
            ( VERINAB42ToCharList A )
        )
        B
    ) = 0
  )
) $.

verina-basic-42-count-digits $a |-
  A. s e. Word VERINAB42Char
    (
      ( VERINAB42Pre s )
      ->
      (
        VERINAB42Post
          s
          ( VERINAB42CountDigits s )
      )
    )
$.
