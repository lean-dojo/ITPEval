$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_7 (verina__metamath__verina_advanced_7), catalog title
  binaryToDecimal: the exact recursive big-endian binary-list program and
  its independently folded decimal-value correctness contract on finite
  natural-number lists whose entries are zero or one. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA7Pre is the source List.all precondition: every input entry is zero
  or one. VERINA7HelperGraph is the exact finite execution graph of the
  source local recursive helper. Its trace starts with zero, the value on the
  empty suffix, and visits the input from right to left. After k entries have
  been processed, the next source clause multiplies the new entry by 2^k
  because the recursive rest has length k, then adds the already computed
  suffix value. VERINA7Helper selects the unique terminal trace value, and
  VERINA7BinaryToDecimal is precisely the source executable implementation.

  VERINA7FoldGraph separately records the postcondition's List.foldl. Its
  accumulator starts at zero and, in left-to-right input order, is replaced
  by twice its previous value plus the current bit. VERINA7Fold selects the
  unique final accumulator. VERINA7NatSub is Lean's truncated Nat.sub, so
  VERINA7Post preserves both source subtraction-equals-zero conjuncts
  literally. The proof-valued precondition argument is computationally and
  propositionally unused inside the program and postcondition, and the final
  assertion supplies it as the explicit antecedent.

  Thus the implementation result is fixed independently of the postcondition;
  the final $a declaration is the complete source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA7Pre
  VERINA7HelperGraph VERINA7Helper VERINA7BinaryToDecimal
  VERINA7FoldGraph VERINA7Fold VERINA7NatSub VERINA7Post
$.

verina7-precondition-syntax
  $a wff ( VERINA7Pre A ) $.
verina7-helper-graph-syntax
  $a wff ( VERINA7HelperGraph A B ) $.
verina7-helper-syntax
  $a class ( VERINA7Helper A ) $.
verina7-program-syntax
  $a class ( VERINA7BinaryToDecimal A ) $.
verina7-fold-graph-syntax
  $a wff ( VERINA7FoldGraph A B ) $.
verina7-fold-syntax
  $a class ( VERINA7Fold A ) $.
verina7-nat-sub-syntax
  $a class ( VERINA7NatSub A B ) $.
verina7-postcondition-syntax
  $a wff ( VERINA7Post A B ) $.

${
  $d k A $.

  verina7-precondition-definition $a |- (
    VERINA7Pre A
  ) <-> (
    A e. Word NN0
    /\
    A. k e. ( 0 ..^ ( # ` A ) )
      ( A ` k ) e. { 0 , 1 }
  ) $.
$}

${
  $d k s A B $.

  verina7-helper-graph-definition $a |- (
    VERINA7HelperGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    E. s e. Word NN0
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = (
              (
                A ` ( ( ( # ` A ) - 1 ) - k )
              )
              x.
              ( 2 ^ k )
              +
              ( s ` k )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina7-helper-definition $a |- (
    VERINA7Helper A
  ) = (
    iota_ y e. NN0
      ( VERINA7HelperGraph A y )
  ) $.
$}

verina7-program-definition $a |- (
  VERINA7BinaryToDecimal A
) = (
  VERINA7Helper A
) $.

${
  $d k s A B $.

  verina7-fold-graph-definition $a |- (
    VERINA7FoldGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    E. s e. Word NN0
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = (
              (
                ( s ` k )
                x.
                2
              )
              +
              ( A ` k )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina7-fold-definition $a |- (
    VERINA7Fold A
  ) = (
    iota_ y e. NN0
      ( VERINA7FoldGraph A y )
  ) $.
$}

verina7-nat-sub-definition $a |- (
  VERINA7NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verina7-postcondition-definition $a |- (
  VERINA7Post A B
) <-> (
  (
    A e. Word NN0
    /\
    B e. NN0
  )
  /\
  (
    (
      VERINA7NatSub
        B
        ( VERINA7Fold A )
    ) = 0
    /\
    (
      VERINA7NatSub
        ( VERINA7Fold A )
        B
    ) = 0
  )
) $.

verina-advanced-7-binary-to-decimal $a |- A. w e. Word NN0
  (
    ( VERINA7Pre w )
    ->
    (
      VERINA7Post
        w
        ( VERINA7BinaryToDecimal w )
    )
  )
$.
