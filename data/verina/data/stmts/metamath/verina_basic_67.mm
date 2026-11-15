$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_67
  (verina__metamath__verina_basic_67), catalog title IsPalindrome: the exact
  executable two-ended scan decides whether an arbitrary finite Unicode
  character list reads identically forward and backward, together with its
  Boolean correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB67Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB67Char represents arbitrary finite Lean lists of characters.
  For a word w, # ` w is its natural-number length, w ` k is zero-based
  lookup, and 0 ..^ n is the set of natural indices below n. The two-element
  set { 0 , 1 } represents Bool with false = 0 and true = 1.

  VERINAB67NatSub is Lean's truncated natural subtraction.
  VERINAB67HelperGraph is the exact graph of isPalindromeHelper for arbitrary
  typed list and natural index arguments. Its witness p counts the successful
  recursive branches already taken. At every earlier branch the left index
  is below the right index, both option lookups are some characters, and the
  characters are equal. The terminal branch returns true exactly when the
  indices have crossed; otherwise it returns false exactly when at least one
  option lookup is none or the two characters differ. Thus the graph admits
  precisely the source recursion's output, including its out-of-range cases.
  VERINAB67Helper selects that unique output.

  VERINAB67Pre is the source True precondition together with the List Char
  input type. VERINAB67IsPalindrome is exactly the source executable
  implementation: the empty list returns true, and every nonempty list calls
  the helper at zero and length minus one. VERINAB67Post preserves the source
  equivalence between a true result and equality of every character with its
  mirrored character. The source's bang lookups are in range under the stated
  index bound, so ordinary word lookup is identical there.

  The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused and are
  represented by the explicit precondition antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this root statement file introduces no $p
  declaration.
$)

$c
  VERINAB67Char VERINAB67NatSub
  VERINAB67HelperGraph VERINAB67Helper
  VERINAB67Pre VERINAB67IsPalindrome VERINAB67Post
$.

verinab67-char-syntax
  $a class VERINAB67Char $.
verinab67-nat-sub-syntax
  $a class ( VERINAB67NatSub A B ) $.
verinab67-helper-graph-syntax
  $a wff ( VERINAB67HelperGraph A B C D ) $.
verinab67-helper-syntax
  $a class ( VERINAB67Helper A B C ) $.
verinab67-precondition-syntax
  $a wff ( VERINAB67Pre A ) $.
verinab67-program-syntax
  $a class ( VERINAB67IsPalindrome A ) $.
verinab67-postcondition-syntax
  $a wff ( VERINAB67Post A B ) $.

verinab67-char-definition $a |- VERINAB67Char =
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

verinab67-nat-sub-definition $a |- (
  VERINAB67NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d k p A B C D $.

  verinab67-helper-graph-definition $a |- (
    VERINAB67HelperGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word VERINAB67Char
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
    E. p e. NN0
      (
        A. k e. ( 0 ..^ p )
          (
            (
              (
                ( B + k ) < ( VERINAB67NatSub C k )
                /\
                ( B + k ) < ( # ` A )
              )
              /\
              ( VERINAB67NatSub C k ) < ( # ` A )
            )
            /\
            (
              A ` ( B + k )
            ) = (
              A ` ( VERINAB67NatSub C k )
            )
          )
        /\
        (
          (
            -. (
              ( B + p ) < ( VERINAB67NatSub C p )
            )
            /\
            D = 1
          )
          \/
          (
            (
              ( B + p ) < ( VERINAB67NatSub C p )
              /\
              (
                -. ( ( B + p ) < ( # ` A ) )
                \/
                (
                  -. (
                    ( VERINAB67NatSub C p ) < ( # ` A )
                  )
                  \/
                  (
                    A ` ( B + p )
                  ) =/= (
                    A ` ( VERINAB67NatSub C p )
                  )
                )
              )
            )
            /\
            D = 0
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab67-helper-definition $a |- (
    VERINAB67Helper A B C
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB67HelperGraph A B C y )
  ) $.
$}

verinab67-precondition-definition $a |- (
  VERINAB67Pre A
) <-> (
  A e. Word VERINAB67Char
) $.

verinab67-program-definition $a |- (
  VERINAB67IsPalindrome A
) = if (
  ( # ` A ) = 0 ,
  1 ,
  (
    VERINAB67Helper
      A
      0
      ( VERINAB67NatSub ( # ` A ) 1 )
  )
) $.

${
  $d i A B $.

  verinab67-postcondition-definition $a |- (
    VERINAB67Post A B
  ) <-> (
    (
      A e. Word VERINAB67Char
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      B = 1
      <->
      A. i e. NN0
        (
          i < ( # ` A )
          ->
          (
            A ` i
          ) = (
            A ` (
              VERINAB67NatSub
                ( VERINAB67NatSub ( # ` A ) i )
                1
            )
          )
        )
    )
  ) $.
$}

verina-basic-67-is-palindrome $a |-
  A. w e. Word VERINAB67Char
    (
      ( VERINAB67Pre w )
      ->
      (
        VERINAB67Post
          w
          ( VERINAB67IsPalindrome w )
      )
    )
$.
