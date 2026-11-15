$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_39
  (verina__metamath__verina_basic_39), catalog title rotateRight: the exact
  executable modular-index map rotates an arbitrary finite integer list to
  the right by a natural count and satisfies its complete length-and-index
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is the index word produced by List.range w.length. Natural
  values embed into ZZ identically, exactly representing Int.ofNat.

  VERINAB39None and VERINAB39Some give a disjoint tagged representation of
  Option Int. VERINAB39GetOption is exactly List.get?: it returns some of the
  indexed entry in bounds and none otherwise. VERINAB39HeadD and
  VERINAB39GetD reproduce List.headD and List.getD with their supplied
  integer defaults. VERINAB39IntMod is Lean Int.emod on all integer inputs:
  modulus zero returns the dividend, and a nonzero divisor uses its positive
  magnitude. VERINAB39ToNat is Lean Int.toNat, returning zero on negatives.

  VERINAB39MapGraph is the exact nonempty branch of the source
  List.range len map. Its output has len entries and at each generated
  natural index i stores
    l.getD (Int.toNat ((i - n + len) % len)) (l.headD 0).
  Finite words are extensional, so these equations characterize one and only
  one output and admit no extra results. VERINAB39RotateRight returns the
  original empty word in the source empty branch and otherwise selects that
  unique mapped word. Thus the executable result is fixed independently of
  the postcondition.

  VERINAB39Pre is the source True precondition on typed List Int and Nat
  inputs. VERINAB39Post preserves the source result-length equation and the
  universal implication over every natural i below the input length, using
  the exact option-valued lookups on both sides. The proof-valued precondition
  arguments are computationally and propositionally unused and are
  represented by the explicit antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB39None VERINAB39Some VERINAB39OptionInt
  VERINAB39GetOption VERINAB39HeadD VERINAB39GetD
  VERINAB39IntMod VERINAB39ToNat
  VERINAB39MapGraph VERINAB39Pre VERINAB39RotateRight VERINAB39Post
$.

verinab39-none-syntax
  $a class VERINAB39None $.
verinab39-some-syntax
  $a class ( VERINAB39Some A ) $.
verinab39-option-int-syntax
  $a class VERINAB39OptionInt $.
verinab39-get-option-syntax
  $a class ( VERINAB39GetOption A B ) $.
verinab39-head-d-syntax
  $a class ( VERINAB39HeadD A B ) $.
verinab39-get-d-syntax
  $a class ( VERINAB39GetD A B C ) $.
verinab39-int-mod-syntax
  $a class ( VERINAB39IntMod A B ) $.
verinab39-to-nat-syntax
  $a class ( VERINAB39ToNat A ) $.
verinab39-map-graph-syntax
  $a wff ( VERINAB39MapGraph A B C ) $.
verinab39-precondition-syntax
  $a wff ( VERINAB39Pre A B ) $.
verinab39-program-syntax
  $a class ( VERINAB39RotateRight A B ) $.
verinab39-postcondition-syntax
  $a wff ( VERINAB39Post A B C ) $.

verinab39-none-definition $a |- VERINAB39None = (/) $.

verinab39-some-definition $a |- (
  VERINAB39Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verinab39-option-int-definition $a |- VERINAB39OptionInt =
    { x |
      (
        x = VERINAB39None
        \/
        E. y e. ZZ
          x = ( VERINAB39Some y )
      )
    } $.
$}

verinab39-get-option-definition $a |- (
  VERINAB39GetOption A B
) = if (
  B < ( # ` A ) ,
  ( VERINAB39Some ( A ` B ) ) ,
  VERINAB39None
) $.

verinab39-head-d-definition $a |- (
  VERINAB39HeadD A B
) = if (
  ( # ` A ) = 0 ,
  B ,
  ( A ` 0 )
) $.

verinab39-get-d-definition $a |- (
  VERINAB39GetD A B C
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  C
) $.

verinab39-int-mod-definition $a |- (
  VERINAB39IntMod A B
) = if (
  B = 0 ,
  A ,
  ( A mod ( abs ` B ) )
) $.

verinab39-to-nat-definition $a |- (
  VERINAB39ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

${
  $d i A B C $.

  verinab39-map-graph-definition $a |- (
    VERINAB39MapGraph A B C
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. NN0
        )
        /\
        C e. Word ZZ
      )
      /\
      0 < ( # ` A )
    )
    /\
    (
      ( # ` C ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          C ` i
        ) = (
          VERINAB39GetD
            A
            (
              VERINAB39ToNat
                (
                  VERINAB39IntMod
                    ( ( i - B ) + ( # ` A ) )
                    ( # ` A )
                )
            )
            ( VERINAB39HeadD A 0 )
        )
    )
  ) $.
$}

verinab39-precondition-definition $a |- (
  VERINAB39Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. NN0
) $.

${
  $d y A B $.

  verinab39-program-definition $a |- (
    VERINAB39RotateRight A B
  ) = if (
    ( # ` A ) = 0 ,
    A ,
    (
      iota_ y e. Word ZZ
        ( VERINAB39MapGraph A B y )
    )
  ) $.
$}

${
  $d i A B C $.

  verinab39-postcondition-definition $a |- (
    VERINAB39Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = ( # ` A )
      /\
      A. i e. NN0
        (
          i < ( # ` A )
          ->
          (
            VERINAB39GetOption C i
          ) = (
            VERINAB39GetOption
              A
              (
                VERINAB39ToNat
                  (
                    VERINAB39IntMod
                      ( ( i - B ) + ( # ` A ) )
                      ( # ` A )
                  )
              )
          )
        )
    )
  ) $.
$}

verina-basic-39-rotate-right $a |- A. l e. Word ZZ
  A. n e. NN0
    (
      ( VERINAB39Pre l n )
      ->
      (
        VERINAB39Post
          l
          n
          ( VERINAB39RotateRight l n )
      )
    )
$.
