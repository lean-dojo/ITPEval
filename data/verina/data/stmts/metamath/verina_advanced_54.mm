$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_54 (verina__metamath__verina_advanced_54), catalog title
  missingNumber: the exact natural-number sum formula applied to an arbitrary
  finite duplicate-free list bounded by its length returns the unique missing
  number from zero through that length. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, ran w is its membership
  set, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA54Bounded is the source List.all condition that every entry is at
  most the list length. VERINA54Nodup is exactly List.Nodup, expressed by
  distinct values at every pair of distinct ordered positions. VERINA54Pre
  combines those clauses with the source List Nat type.

  VERINA54ExpectedSum is floor(n * (n + 1) / 2), exactly Lean Nat.div; the
  numerator is always even, but retaining floor makes the natural-division
  semantics explicit. VERINA54ActualSum is the finite sum of every indexed
  entry. By the associative identity laws for natural addition, this is
  exactly nums.foldl (fun a b => a + b) 0. VERINA54NatSub restores Lean's
  truncated Nat.sub rather than SetMM's ordinary integer subtraction.
  VERINA54MissingNumber applies that exact subtraction to the two source
  let-bound values, so its result is fixed independently of the postcondition.

  VERINA54Post says that the result lies in List.range (length + 1), is absent
  from the input, and every other member of that range occurs in the input.
  Bounded quantification over 0 ..^ (length + 1) is bidirectionally equivalent
  to the source universal implication from List.range membership. The Lean
  proof-valued precondition argument is computationally unused and is
  represented by the explicit antecedent of the final assertion. The final
  $a declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA54Bounded VERINA54Nodup VERINA54Pre
  VERINA54ExpectedSum VERINA54ActualSum VERINA54NatSub
  VERINA54MissingNumber VERINA54Post
$.

verina54-bounded-syntax
  $a wff ( VERINA54Bounded A ) $.
verina54-nodup-syntax
  $a wff ( VERINA54Nodup A ) $.
verina54-precondition-syntax
  $a wff ( VERINA54Pre A ) $.
verina54-expected-sum-syntax
  $a class ( VERINA54ExpectedSum A ) $.
verina54-actual-sum-syntax
  $a class ( VERINA54ActualSum A ) $.
verina54-nat-sub-syntax
  $a class ( VERINA54NatSub A B ) $.
verina54-missing-number-syntax
  $a class ( VERINA54MissingNumber A ) $.
verina54-postcondition-syntax
  $a wff ( VERINA54Post A B ) $.

${
  $d i A $.

  verina54-bounded-definition $a |- (
    VERINA54Bounded A
  ) <-> (
    (
      A e. Word NN0
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( A ` i ) <_ ( # ` A )
    )
  ) $.
$}

${
  $d i j A $.

  verina54-nodup-definition $a |- (
    VERINA54Nodup A
  ) <-> (
    (
      A e. Word NN0
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) =/= ( A ` j )
          )
    )
  ) $.
$}

verina54-precondition-definition $a |- (
  VERINA54Pre A
) <-> (
  (
    A e. Word NN0
    /\
    (
      ( VERINA54Bounded A )
      /\
      ( VERINA54Nodup A )
    )
  )
) $.

verina54-expected-sum-definition $a |- (
  VERINA54ExpectedSum A
) = (
  |_ ` (
    (
      ( # ` A )
      x.
      ( ( # ` A ) + 1 )
    )
    /
    2
  )
) $.

${
  $d k A $.

  verina54-actual-sum-definition $a |- (
    VERINA54ActualSum A
  ) = (
    sum_ k e. ( 0 ..^ ( # ` A ) )
      ( A ` k )
  ) $.
$}

verina54-nat-sub-definition $a |- (
  VERINA54NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verina54-missing-number-definition $a |- (
  VERINA54MissingNumber A
) = (
  VERINA54NatSub
    ( VERINA54ExpectedSum A )
    ( VERINA54ActualSum A )
) $.

${
  $d x A B $.

  verina54-postcondition-definition $a |- (
    VERINA54Post A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    (
      (
        B e. ( 0 ..^ ( ( # ` A ) + 1 ) )
        /\
        -. ( B e. ran A )
      )
      /\
      A. x e. ( 0 ..^ ( ( # ` A ) + 1 ) )
        (
          x =/= B
          ->
          x e. ran A
        )
    )
  ) $.
$}

verina-advanced-54-missing-number
  $a |- A. w e. Word NN0
    (
      ( VERINA54Pre w )
      ->
      (
        VERINA54Post
          w
          ( VERINA54MissingNumber w )
      )
    )
  $.
