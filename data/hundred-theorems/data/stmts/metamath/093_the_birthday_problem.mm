$(
  Statement-only formalization of "The Birthday Problem" from Hundred
  Theorems corpus artifact 093: among assignments of birthdays to people,
  collisions occur in more than half of the 23-person assignments and fewer
  than half of the 22-person assignments when there are 365 possible
  birthdays. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The finite interval 1 ... n is used as an n-element carrier. Thus the
  function classes below have the same cardinalities as functions between
  Fin n types. The first inequality says that injective assignments for 23
  people are fewer than half of all assignments; the second says that
  injective assignments for 22 people are more than half of all assignments.
  Since every assignment is exactly one of injective or colliding, these are
  equivalent to the two collision inequalities in the source statements.

  The declaration is an unproved $a assertion. There is no $p proof statement
  in this file.
$)

hundred-theorems-093-birthday-problem $a
  |- (
    (
      ( 2 x.
        ( # `
          { f |
            f : ( 1 ... ; 2 3 ) -1-1-> ( 1 ... ; ; 3 6 5 )
          }
        )
      )
      <
      ( # `
        { f |
          f : ( 1 ... ; 2 3 ) --> ( 1 ... ; ; 3 6 5 )
        }
      )
    )
    /\
    (
      ( # `
        { f |
          f : ( 1 ... ; 2 2 ) --> ( 1 ... ; ; 3 6 5 )
        }
      )
      <
      ( 2 x.
        ( # `
          { f |
            f : ( 1 ... ; 2 2 ) -1-1-> ( 1 ... ; ; 3 6 5 )
          }
        )
      )
    )
  )
$.
