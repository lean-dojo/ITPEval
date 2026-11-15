$(
  Statement-only formalization of Thousand Theorems corpus artifact Q182505
  (thousand-theorems__metamath__Q182505), "Bayes' theorem": for an arbitrary
  finite measure and measurable sets, conditional probabilities satisfy
  Bayes' identity in the extended nonnegative reals. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Q182505ENNInv is the reciprocal on the extended nonnegative reals, with
  zero and positive infinity interchanged. Q182505Cond M A B is the
  conditional probability of A given B, defined exactly as the measure of
  B inverse times the measure of B intersect A.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q182505ENNInv Q182505Cond $.

q182505-enn-inv-syntax $a class ( Q182505ENNInv A ) $.
q182505-cond-syntax $a class ( Q182505Cond M A B ) $.

${
  q182505-enn-inv-definition $a |- (
    Q182505ENNInv A
  ) =
    if
    (
      A = 0 ,
      +oo ,
      if
      (
        A = +oo ,
        0 ,
        ( 1 / A )
      )
    )
  $.
$}

${
  $d A B M $.

  q182505-cond-definition $a |- (
    Q182505Cond M A B
  ) =
    (
      ( Q182505ENNInv ( M ` B ) )
      *e
      ( M ` ( B i^i A ) )
    )
  $.
$}

${
  $d A B M $.

  thousand-theorems-q182505-bayes-theorem $a |-
    A. M e. U. ran measures
      A. A e. dom M
        A. B e. dom M
          (
            ( M ` U. dom M ) =/= +oo
            ->
            (
              ( Q182505Cond M B A )
              =
              (
                (
                  ( Q182505ENNInv ( M ` A ) )
                  *e
                  ( Q182505Cond M A B )
                )
                *e
                ( M ` B )
              )
            )
          )
  $.
$}
