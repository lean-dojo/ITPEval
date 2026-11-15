$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_14
  (verina__metamath__verina_basic_14), catalog title containsZ: the exact
  executable Boolean string scan returns true exactly when an arbitrary
  Unicode string contains lowercase z or uppercase Z, together with its
  existential membership correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB14Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB14Char represents arbitrary Lean strings extensionally through
  String.toList. Word lookup is zero-based, and 0 ..^ ( # ` A ) is the
  complete valid-index set of the represented character list.

  VERINAB14HasZ is true exactly when some character of the input word is code
  point 122 or 90, respectively Lean's 'z' and 'Z'. This is the exact
  existential characterization of both the source equality-disjunction
  predicate and List.any scan. VERINAB14ContainsZ returns one precisely in
  that case and zero otherwise, so the executable result is fixed
  independently of the postcondition and admits no additional outputs.

  VERINAB14Pre is the source True precondition on typed String inputs.
  VERINAB14Post preserves the source equivalence between existential
  character membership and the Boolean result. The proof-valued precondition
  argument is computationally and propositionally unused and is represented
  by the explicit antecedent of the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB14Char VERINAB14HasZ
  VERINAB14Pre VERINAB14ContainsZ VERINAB14Post
$.

verinab14-char-syntax
  $a class VERINAB14Char $.
verinab14-has-z-syntax
  $a wff ( VERINAB14HasZ A ) $.
verinab14-precondition-syntax
  $a wff ( VERINAB14Pre A ) $.
verinab14-program-syntax
  $a class ( VERINAB14ContainsZ A ) $.
verinab14-postcondition-syntax
  $a wff ( VERINAB14Post A B ) $.

verinab14-char-definition $a |- VERINAB14Char =
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

${
  $d i A $.

  verinab14-has-z-definition $a |- (
    VERINAB14HasZ A
  ) <-> (
    A e. Word VERINAB14Char
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      (
        ( A ` i ) = ; ; 1 2 2
        \/
        ( A ` i ) = ; 9 0
      )
  ) $.
$}

verinab14-precondition-definition $a |- (
  VERINAB14Pre A
) <-> (
  A e. Word VERINAB14Char
) $.

verinab14-program-definition $a |- (
  VERINAB14ContainsZ A
) = if (
  ( VERINAB14HasZ A ) ,
  1 ,
  0
) $.

verinab14-postcondition-definition $a |- (
  VERINAB14Post A B
) <-> (
  (
    A e. Word VERINAB14Char
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    ( VERINAB14HasZ A )
    <->
    B = 1
  )
) $.

verina-basic-14-contains-z $a |- A. w e. Word VERINAB14Char
  (
    ( VERINAB14Pre w )
    ->
    (
      VERINAB14Post
        w
        ( VERINAB14ContainsZ w )
    )
  )
$.
