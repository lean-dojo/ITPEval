$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_39 (verina__metamath__verina_advanced_39), catalog title
  maxOfList: the exact recursive natural-number list program returns an
  element of every nonempty input list that bounds all its elements above.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA39HelperGraph gives the exact computation of the source local helper.
  Its trace begins at zero, the result for the empty list, and visits the
  input from right to left. At each step it returns the current element when
  that element is greater than the recursively computed tail result, and
  otherwise retains the tail result. For a singleton, comparison with the
  initial zero returns its sole natural-number element, exactly matching the
  source singleton branch. VERINA39Helper selects the unique trace result,
  and VERINA39MaxOfList is the source executable implementation.

  VERINA39Pre is the positive-length precondition. VERINA39Post says that the
  result occurs at an input position and that every input position contains
  a value at most the result, exactly representing List membership and the
  source boundedness clause. The proof-valued precondition argument is
  computationally and propositionally unused and is omitted from the target
  function and predicate. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no $p declaration.
$)

$c
  VERINA39HelperGraph VERINA39Helper
  VERINA39Pre VERINA39MaxOfList VERINA39Post
$.

verina39-helper-graph-syntax
  $a wff ( VERINA39HelperGraph A B ) $.
verina39-helper-syntax
  $a class ( VERINA39Helper A ) $.
verina39-precondition-syntax
  $a wff ( VERINA39Pre A ) $.
verina39-max-of-list-syntax
  $a class ( VERINA39MaxOfList A ) $.
verina39-postcondition-syntax
  $a wff ( VERINA39Post A B ) $.

${
  $d k s A B $.

  verina39-helper-graph-definition $a |- (
    VERINA39HelperGraph A B
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
              if (
                (
                  s ` k
                ) < (
                  A ` ( ( ( # ` A ) - 1 ) - k )
                )
                ,
                (
                  A ` ( ( ( # ` A ) - 1 ) - k )
                )
                ,
                ( s ` k )
              )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina39-helper-definition $a |- (
    VERINA39Helper A
  ) = (
    iota_ y e. NN0
      ( VERINA39HelperGraph A y )
  ) $.
$}

verina39-precondition-definition $a |- (
  VERINA39Pre A
) <-> (
  A e. Word NN0
  /\
  0 < ( # ` A )
) $.

verina39-max-of-list-definition $a |- (
  VERINA39MaxOfList A
) = (
  VERINA39Helper A
) $.

${
  $d i j A B $.

  verina39-postcondition-definition $a |- (
    VERINA39Post A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    (
      E. i e. ( 0 ..^ ( # ` A ) )
        ( A ` i ) = B
      /\
      A. j e. ( 0 ..^ ( # ` A ) )
        ( A ` j ) <_ B
    )
  ) $.
$}

verina-advanced-39-max-of-list $a |- A. w e. Word NN0
  (
    ( VERINA39Pre w )
    ->
    (
      VERINA39Post
        w
        ( VERINA39MaxOfList w )
    )
  )
$.
