$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1047749
  (thousand-theorems__metamath__Q1047749), "Turan's theorem": for a positive
  natural number r, a finite simple graph is maximal by edge count among
  graphs with no clique of size r + 1 exactly when it is isomorphic to the
  canonical Turan graph with adjacency determined by unequal residues
  modulo r. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Finite Lean vertex types are represented by arbitrary finite sets V.
  Q1047749SimpleGraph says that G is an irreflexive symmetric relation on V.
  Q1047749CliqueFree excludes a subset of V of the specified finite
  cardinality whose distinct vertices are pairwise adjacent.

  Q1047749Edges is the set of unordered two-element edges. Thus its finite
  cardinality is the source edgeFinset cardinality. Q1047749TuranMaximal
  states both (r + 1)-clique-freeness and maximal edge count among all simple
  graphs on the same vertex set satisfying that condition.

  Q1047749IsoTuran internally quantifies a bijection from V to the canonical
  n-element set 0 ..^ (# V) and requires adjacency to correspond in both
  directions to unequal residues modulo r. This is exactly graph
  isomorphism with turanGraph (card V) r; no witness has been externalized.

  The final declaration is the single unproved corpus $a statement. The
  preceding $a declarations are syntax and faithful definitions only. This
  file introduces no $p proof statement.
$)

$c Q1047749SimpleGraph Q1047749CliqueFree Q1047749Edges $.
$c Q1047749TuranMaximal Q1047749IsoTuran $.

q1047749-simple-graph-syntax $a
  wff ( Q1047749SimpleGraph V G ) $.
q1047749-clique-free-syntax $a
  wff ( Q1047749CliqueFree V G r ) $.
q1047749-edges-syntax $a
  class ( Q1047749Edges V G ) $.
q1047749-turan-maximal-syntax $a
  wff ( Q1047749TuranMaximal V G r ) $.
q1047749-iso-turan-syntax $a
  wff ( Q1047749IsoTuran V G r ) $.

${
  $d G V u v $.

  q1047749-simple-graph-definition $a |- (
    ( Q1047749SimpleGraph V G )
    <->
    (
      G C_ ( V X. V )
      /\
      (
        A. u e. V -. <. u , u >. e. G
        /\
        A. u e. V A. v e. V
          ( <. u , v >. e. G -> <. v , u >. e. G )
      )
    )
  ) $.
$}

${
  $d G K V r u v $.

  q1047749-clique-free-definition $a |- (
    ( Q1047749CliqueFree V G r )
    <->
    -.
    E. K
      (
        (
          K C_ V
          /\
          ( # ` K ) = r
        )
        /\
        A. u e. K A. v e. K
          ( u =/= v -> <. u , v >. e. G )
      )
  ) $.
$}

${
  $d G K V u v $.

  q1047749-edges-definition $a |- (
    ( Q1047749Edges V G )
    =
    { K e. ~P V |
      E. u e. V E. v e. V
        (
          K = { u , v }
          /\
          (
            u =/= v
            /\
            <. u , v >. e. G
          )
        )
    }
  ) $.
$}

${
  $d G H V r $.

  q1047749-turan-maximal-definition $a |- (
    ( Q1047749TuranMaximal V G r )
    <->
    (
      ( Q1047749SimpleGraph V G )
      /\
      (
        ( Q1047749CliqueFree V G ( r + 1 ) )
        /\
        A. H
          (
            (
              ( Q1047749SimpleGraph V H )
              /\
              ( Q1047749CliqueFree V H ( r + 1 ) )
            )
            ->
            (
              ( # ` ( Q1047749Edges V H ) )
              <_
              ( # ` ( Q1047749Edges V G ) )
            )
          )
      )
    )
  ) $.
$}

${
  $d G V f r u v $.

  q1047749-iso-turan-definition $a |- (
    ( Q1047749IsoTuran V G r )
    <->
    E. f
      (
        f : V -1-1-onto-> ( 0 ..^ ( # ` V ) )
        /\
        A. u e. V A. v e. V
          (
            <. u , v >. e. G
            <->
            ( ( ( f ` u ) mod r ) =/= ( ( f ` v ) mod r ) )
          )
      )
  ) $.
$}

${
  $d G V r $.

  thousand-theorems-q1047749-turan $a |- (
    A. V A. G A. r
      (
        (
          (
            V e. Fin
            /\
            r e. NN
          )
          /\
          ( Q1047749SimpleGraph V G )
        )
        ->
        (
          ( Q1047749TuranMaximal V G r )
          <->
          ( Q1047749IsoTuran V G r )
        )
      )
  ) $.
$}
