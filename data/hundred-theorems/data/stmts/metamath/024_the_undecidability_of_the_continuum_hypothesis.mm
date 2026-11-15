$(
  Statement-only formalization of "The Undecidability of the Continuum
  Hypothesis" from Hundred Theorems item 024: every countable transitive set
  model of ZF has a proper countable transitive ZF extension with the same
  ordinals, and Choice in the source model implies ZFC in the extension.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The predicates below are grounded in set.mm. HT024ZFModels is the class of
  sets satisfying the six displayed Godel-coded ZF axioms and every instance
  of the Godel-coded Replacement scheme. Transitivity remains a separate
  condition, exactly as in the Isabelle source.

  HT024AxChoice is the closed pure-membership sentence saying that every
  pairwise-disjoint family of nonempty sets has a choice set meeting each
  family member in exactly one element. Over ZF this is equivalent to the
  source's axiom of choice. Since the code is closed, set.mm validity
  M |= HT024AxChoice is equivalent to satisfaction under the empty assignment.

  HT024ZFCModels is defined as ZF satisfaction together with satisfaction of
  this Choice sentence. The final declaration is an unproved $a statement;
  the artifact adds no proof.
$)

$c HT024AxChoice HT024ZFModels HT024ZFCModels $.

ht024-choice-syntax $a class HT024AxChoice $.
ht024-zf-models-syntax $a class HT024ZFModels $.
ht024-zfc-models-syntax $a class HT024ZFCModels $.

$(
  Variable indices in HT024AxChoice are:
    0 family, 1 and 2 family members, 3 selected element, and 4 choice set.
  Index 2 is reused as the comparison element after its earlier scope ends.
$)
ht024-choice-definition $a |- HT024AxChoice =
  A.g (/) (
    (
      (
        A.g 1o (
          ( 1o e.g (/) )
          ->g
          E.g 2o ( 2o e.g 1o )
        )
        /\g
        A.g 1o A.g 2o (
          (
            (
              ( 1o e.g (/) )
              /\g
              ( 2o e.g (/) )
            )
            /\g
            -.g ( 1o =g 2o )
          )
          ->g
          -.g E.g 3o (
            ( 3o e.g 1o )
            /\g
            ( 3o e.g 2o )
          )
        )
      )
      ->g
      E.g 4o A.g 1o (
        ( 1o e.g (/) )
        ->g
        E.g 3o (
          (
            ( 3o e.g 1o )
            /\g
            ( 3o e.g 4o )
          )
          /\g
          A.g 2o (
            (
              ( 2o e.g 1o )
              /\g
              ( 2o e.g 4o )
            )
            ->g
            ( 2o =g 3o )
          )
        )
      )
    )
  ) $.

${
  $d m u $.
  ht024-zf-models-definition $a |- HT024ZFModels = { m |
    (
      ( m |= AxExt /\ m |= AxPow )
      /\
      ( m |= AxUn /\ m |= AxReg )
      /\
      (
        m |= AxInf
        /\
        A. u e. ( Fmla ` _om ) m |= ( AxRep ` u )
      )
    )
  } $.
$}

ht024-zfc-models-definition $a |- HT024ZFCModels = { m |
  (
    m e. HT024ZFModels
    /\
    m |= HT024AxChoice
  )
} $.

${
  $d M n a $.
  ht024-source-model-countable $e |- M ~~ _om $.
  ht024-source-model-transitive $e |- Tr M $.
  ht024-source-model-zf $e |- M e. HT024ZFModels $.

  extensions-of-ctms $a |- (
    E. n (
      M C_ n
      /\
      (
        n ~~ _om
        /\
        (
          Tr n
          /\
          (
            n e. HT024ZFModels
            /\
            (
              M =/= n
              /\
              (
                (
                  A. a (
                    Ord a
                    ->
                    (
                      a e. M
                      <->
                      a e. n
                    )
                  )
                )
                /\
                (
                  M |= HT024AxChoice
                  ->
                  n e. HT024ZFCModels
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}
