$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/patience_PatienceCode_push_cardqtvc: the patience-solitaire push-card
  verification condition preserves the invariant that every stack is
  nonempty while either placing a card on the first eligible stack or
  continuing through the remaining stacks. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM Word ZZ is exactly the type of arbitrary finite zero-based integer
  lists, and Word ( Word ZZ ) is exactly the type of arbitrary finite lists
  of such stacks. NTP4VCWFStacks is definitionally equivalent to the source
  recursive wf_stacks predicate: every member stack is nonempty.

  NTP4VCReverse is exact finite-list reversal. NTP4VCTailEq retains the
  repeated source match that identifies the tail of stacks1. The two branch
  predicates expand the source pattern matches; proposition-valued if is
  represented by exhaustive guarded disjunctions. Empty inner stacks have no
  branch, exactly matching the source False case. Every result remains
  universally quantified inside the verification condition.

  Expanding these definitions recovers the Why3 verification condition and
  the agreeing Lean, Rocq, and Isabelle exports. Every auxiliary $a below is
  syntax or a faithful definitional abbreviation. The final $a declaration is
  Metamath's native unproved statement encoding; this database contains no $p
  declaration.
$)

$c
  NTP4VCWFStacks NTP4VCReverse NTP4VCTailEq
  NTP4VCInvariantBranch NTP4VCRun NTP4VCPushCardVC
$.

ntp4vc-wf-stacks-syntax
  $a wff ( NTP4VCWFStacks A ) $.
ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-tail-eq-syntax
  $a wff ( NTP4VCTailEq A B ) $.
ntp4vc-invariant-branch-syntax
  $a wff ( NTP4VCInvariantBranch A B C ) $.
ntp4vc-run-syntax
  $a wff ( NTP4VCRun A B C D ) $.
ntp4vc-push-card-vc-syntax
  $a wff ( NTP4VCPushCardVC A B C ) $.

${
  $d i A $.

  ntp4vc-wf-stacks-definition $a |- (
    NTP4VCWFStacks A
  ) <->
  (
    A e. Word ( Word ZZ )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      ( A ` i ) =/= (/)
  ) $.
$}

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

${
  $d s A B $.

  ntp4vc-tail-eq-definition $a |- (
    NTP4VCTailEq A B
  ) <->
  E. s e. Word ZZ
    A = ( <" s "> ++ B ) $.
$}

${
  $d r s t x A B C $.

  ntp4vc-invariant-branch-definition $a |- (
    NTP4VCInvariantBranch A B C
  ) <->
  (
    A = (/)
    \/
    E. s e. Word ZZ E. r e. Word ( Word ZZ )
      (
        A = ( <" s "> ++ r )
        /\
        E. x e. ZZ E. t e. Word ZZ
          (
            s = ( <" x "> ++ t )
            /\
            (
              -. C <_ x
              ->
              (
                ( NTP4VCTailEq A r )
                /\
                (
                  ( NTP4VCWFStacks r )
                  /\
                  (
                    NTP4VCWFStacks
                      ( <" s "> ++ B )
                  )
                )
              )
            )
          )
      )
  ) $.
$}

${
  $d r s t x A B C D $.

  ntp4vc-run-definition $a |- (
    NTP4VCRun A B C D
  ) <->
  (
    (
      A = (/)
      /\
      D = (
        (
          NTP4VCReverse
            ( <" ( <" C "> ) "> ++ B )
        )
        ++
        (/)
      )
    )
    \/
    E. s e. Word ZZ E. r e. Word ( Word ZZ )
      (
        A = ( <" s "> ++ r )
        /\
        E. x e. ZZ E. t e. Word ZZ
          (
            s = ( <" x "> ++ t )
            /\
            (
              (
                C <_ x
                /\
                D = (
                  (
                    NTP4VCReverse
                      (
                        <" ( <" C "> ++ s ) ">
                        ++
                        B
                      )
                  )
                  ++
                  r
                )
              )
              \/
              (
                -. C <_ x
                /\
                ( NTP4VCWFStacks D )
              )
            )
          )
      )
  ) $.
$}

${
  $d q A B C $.

  ntp4vc-push-card-vc-definition $a |- (
    NTP4VCPushCardVC A B C
  ) <->
  (
    ( NTP4VCInvariantBranch A B C )
    /\
    A. q e. Word ( Word ZZ )
      (
        ( NTP4VCRun A B C q )
        ->
        ( NTP4VCWFStacks q )
      )
  ) $.
$}

${
  $d i q r s t x A B C $.

  ntp4vc-stacks1-list
    $e |- A e. Word ( Word ZZ ) $.
  ntp4vc-acc-list
    $e |- B e. Word ( Word ZZ ) $.
  ntp4vc-card-integer
    $e |- C e. ZZ $.

  ntp4vc-fact0
    $e |- ( NTP4VCWFStacks A ) $.
  ntp4vc-fact1
    $e |- ( NTP4VCWFStacks B ) $.

  ntp4vc-pearl-patience-patience-code-push-card-vc $a |- (
    NTP4VCPushCardVC A B C
  ) $.
$}
