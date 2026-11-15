;; Statement-only formalization of thousand-theorems corpus artifact Q1687147,
;; "Sprague–Grundy theorem": every arbitrary well-founded impartial game is
;; equivalent to the game of Nim indexed by its recursively defined Grundy
;; value. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame function objects represent arbitrary, potentially infinite carriers,
;; move relations, ordinal well-orders, and recursively characterized semantic
;; predicates. No carrier is enumerated or restricted to finite game trees.

(defun q1687147-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q1687147-relation-p (relation left right)
  (if (apply$ relation (list left right)) t nil))

(defun q1687147-map-value (map object)
  (apply$ map (list object)))

(defun q1687147-option-p (left-move right-move parent child)
  (or
   (q1687147-relation-p left-move parent child)
   (q1687147-relation-p right-move parent child)))

;; A game carrier is closed under both kinds of moves, and the union of its
;; move relations is well-founded. Well-foundedness is expressed by the
;; equivalent least-element property for every arbitrary tame subset.

(defun-sk q1687147-moves-closed-p
    (carrier left-move right-move)
  (forall (parent child)
    (implies
     (and
      (q1687147-member-p carrier parent)
      (q1687147-option-p
       left-move right-move parent child))
     (q1687147-member-p carrier child))))

(defun-sk q1687147-subset-of-p (carrier subset)
  (forall (object)
    (implies
     (q1687147-member-p subset object)
     (q1687147-member-p carrier object))))

(defun-sk q1687147-subset-nonempty-p (carrier subset)
  (exists (object)
    (and
     (q1687147-member-p carrier object)
     (q1687147-member-p subset object))))

(defun-sk q1687147-no-subset-option-p
    (subset left-move right-move object)
  (forall (child)
    (implies
     (q1687147-option-p
      left-move right-move object child)
     (not (q1687147-member-p subset child)))))

(defun q1687147-subset-minimal-p
    (carrier subset left-move right-move object)
  (and
   (q1687147-member-p carrier object)
   (q1687147-member-p subset object)
   (q1687147-no-subset-option-p
    subset left-move right-move object)))

(defun-sk q1687147-subset-minimal-exists-p
    (carrier subset left-move right-move)
  (exists (object)
    (q1687147-subset-minimal-p
     carrier subset left-move right-move object)))

(defun-sk q1687147-game-well-founded-p
    (carrier left-move right-move)
  (forall (subset)
    (implies
     (and
      (tamep-functionp subset)
      (q1687147-subset-of-p carrier subset)
      (q1687147-subset-nonempty-p carrier subset))
     (q1687147-subset-minimal-exists-p
      carrier subset left-move right-move))))

(defun q1687147-game-p
    (carrier left-move right-move root)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left-move)
   (tamep-functionp right-move)
   (q1687147-member-p carrier root)
   (q1687147-moves-closed-p
    carrier left-move right-move)
   (q1687147-game-well-founded-p
    carrier left-move right-move)))

;; Nimber values are represented by an arbitrary strict well-order. Every
;; such well-order is isomorphic to an ordinal, so this preserves the source's
;; ordinal-indexed Nim games without imposing ACL2's executable ordinal bound.

(defun-sk q1687147-strict-order-laws-p (carrier less)
  (forall (x y z)
    (and
     (implies
      (q1687147-member-p carrier x)
      (not (q1687147-relation-p less x x)))
     (implies
      (and
       (q1687147-member-p carrier x)
       (q1687147-member-p carrier y))
      (or
       (q1687147-relation-p less x y)
       (equal x y)
       (q1687147-relation-p less y x)))
     (implies
      (and
       (q1687147-member-p carrier x)
       (q1687147-member-p carrier y)
       (q1687147-member-p carrier z)
       (q1687147-relation-p less x y)
       (q1687147-relation-p less y z))
      (q1687147-relation-p less x z)))))

(defun-sk q1687147-no-smaller-subset-member-p
    (subset less object)
  (forall (other)
    (implies
     (q1687147-member-p subset other)
     (not (q1687147-relation-p less other object)))))

(defun q1687147-least-subset-member-p
    (carrier subset less object)
  (and
   (q1687147-member-p carrier object)
   (q1687147-member-p subset object)
   (q1687147-no-smaller-subset-member-p
    subset less object)))

(defun-sk q1687147-least-subset-member-exists-p
    (carrier subset less)
  (exists (object)
    (q1687147-least-subset-member-p
     carrier subset less object)))

(defun-sk q1687147-order-well-founded-p (carrier less)
  (forall (subset)
    (implies
     (and
      (tamep-functionp subset)
      (q1687147-subset-of-p carrier subset)
      (q1687147-subset-nonempty-p carrier subset))
     (q1687147-least-subset-member-exists-p
      carrier subset less))))

(defun q1687147-well-order-p (carrier less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp less)
   (q1687147-strict-order-laws-p carrier less)
   (q1687147-order-well-founded-p carrier less)))

;; Positions combine the source game, its formal negative, and Nim positions.
;; Negation swaps left and right moves, while Nim(o) has every smaller ordinal
;; as both a left and a right option.

(defun q1687147-positive-position (node)
  (list :source :positive node))

(defun q1687147-negative-position (node)
  (list :source :negative node))

(defun q1687147-nim-position (ordinal)
  (list :nim ordinal))

(defun q1687147-positive-position-p (position)
  (and
   (true-listp position)
   (equal (len position) 3)
   (equal (car position) :source)
   (equal (cadr position) :positive)))

(defun q1687147-negative-position-p (position)
  (and
   (true-listp position)
   (equal (len position) 3)
   (equal (car position) :source)
   (equal (cadr position) :negative)))

(defun q1687147-nim-position-p (position)
  (and
   (true-listp position)
   (equal (len position) 2)
   (equal (car position) :nim)))

(defun q1687147-position-p
    (game-carrier ordinal-carrier position)
  (cond
   ((q1687147-positive-position-p position)
    (q1687147-member-p game-carrier (caddr position)))
   ((q1687147-negative-position-p position)
    (q1687147-member-p game-carrier (caddr position)))
   ((q1687147-nim-position-p position)
    (q1687147-member-p ordinal-carrier (cadr position)))
   (t nil)))

(defun q1687147-position-left-move-p
    (left-move right-move ordinal-less parent child)
  (cond
   ((q1687147-positive-position-p parent)
    (and
     (q1687147-positive-position-p child)
     (q1687147-relation-p
      left-move (caddr parent) (caddr child))))
   ((q1687147-negative-position-p parent)
    (and
     (q1687147-negative-position-p child)
     (q1687147-relation-p
      right-move (caddr parent) (caddr child))))
   ((q1687147-nim-position-p parent)
    (and
     (q1687147-nim-position-p child)
     (q1687147-relation-p
      ordinal-less (cadr child) (cadr parent))))
   (t nil)))

(defun q1687147-position-right-move-p
    (left-move right-move ordinal-less parent child)
  (cond
   ((q1687147-positive-position-p parent)
    (and
     (q1687147-positive-position-p child)
     (q1687147-relation-p
      right-move (caddr parent) (caddr child))))
   ((q1687147-negative-position-p parent)
    (and
     (q1687147-negative-position-p child)
     (q1687147-relation-p
      left-move (caddr parent) (caddr child))))
   ((q1687147-nim-position-p parent)
    (and
     (q1687147-nim-position-p child)
     (q1687147-relation-p
      ordinal-less (cadr child) (cadr parent))))
   (t nil)))

;; Conway's recursive order is characterized by its exact defining equation:
;; G <= H iff no left option of G is >= H and no right option of H is <= G.
;; On well-founded games this equation uniquely defines the source relation.

(defun q1687147-game-le-p (game-le left right)
  (q1687147-relation-p game-le left right))

(defun-sk q1687147-no-left-refutation-p
    (game-carrier ordinal-carrier left-move right-move ordinal-less
     game-le left right)
  (forall (option)
    (implies
     (and
      (q1687147-position-p
       game-carrier ordinal-carrier option)
      (q1687147-position-left-move-p
       left-move right-move ordinal-less left option))
     (not (q1687147-game-le-p game-le right option)))))

(defun-sk q1687147-no-right-refutation-p
    (game-carrier ordinal-carrier left-move right-move ordinal-less
     game-le left right)
  (forall (option)
    (implies
     (and
      (q1687147-position-p
       game-carrier ordinal-carrier option)
      (q1687147-position-right-move-p
       left-move right-move ordinal-less right option))
     (not (q1687147-game-le-p game-le option left)))))

(defun q1687147-game-le-equation-p
    (game-carrier ordinal-carrier left-move right-move ordinal-less
     game-le left right)
  (iff
   (q1687147-game-le-p game-le left right)
   (and
    (q1687147-no-left-refutation-p
     game-carrier ordinal-carrier left-move right-move ordinal-less
     game-le left right)
    (q1687147-no-right-refutation-p
     game-carrier ordinal-carrier left-move right-move ordinal-less
     game-le left right))))

(defun-sk q1687147-game-le-semantics-p
    (game-carrier ordinal-carrier left-move right-move ordinal-less
     game-le)
  (forall (left right)
    (implies
     (and
      (q1687147-position-p
       game-carrier ordinal-carrier left)
      (q1687147-position-p
       game-carrier ordinal-carrier right))
     (q1687147-game-le-equation-p
      game-carrier ordinal-carrier left-move right-move ordinal-less
      game-le left right))))

(defun q1687147-game-equiv-p (game-le left right)
  (and
   (q1687147-game-le-p game-le left right)
   (q1687147-game-le-p game-le right left)))

;; The source's Impartial class says that a game is equivalent to its negative
;; and that each of its left and right options is recursively impartial.

(defun-sk q1687147-all-options-impartial-p
    (left-move right-move impartial node)
  (forall (child)
    (implies
     (q1687147-option-p left-move right-move node child)
     (q1687147-member-p impartial child))))

(defun q1687147-impartial-equation-p
    (left-move right-move game-le impartial node)
  (iff
   (q1687147-member-p impartial node)
   (and
    (q1687147-game-equiv-p
     game-le
     (q1687147-positive-position node)
     (q1687147-negative-position node))
    (q1687147-all-options-impartial-p
     left-move right-move impartial node))))

(defun-sk q1687147-impartial-semantics-p
    (game-carrier left-move right-move game-le impartial)
  (forall (node)
    (implies
     (q1687147-member-p game-carrier node)
     (q1687147-impartial-equation-p
      left-move right-move game-le impartial node))))

;; The right Grundy value is the minimum excluded ordinal: it is absent from
;; the right-option values, and every smaller ordinal occurs among them.

(defun-sk q1687147-grundy-value-absent-p
    (right-move grundy node value)
  (forall (child)
    (implies
     (q1687147-relation-p right-move node child)
     (not
      (equal
       (q1687147-map-value grundy child)
       value)))))

(defun-sk q1687147-lower-grundy-value-attained-p
    (right-move grundy node value)
  (exists (child)
    (and
     (q1687147-relation-p right-move node child)
     (equal
      (q1687147-map-value grundy child)
      value))))

(defun-sk q1687147-all-lower-grundy-values-attained-p
    (ordinal-carrier ordinal-less right-move grundy node value)
  (forall (lower)
    (implies
     (and
      (q1687147-member-p ordinal-carrier lower)
      (q1687147-relation-p ordinal-less lower value))
     (q1687147-lower-grundy-value-attained-p
      right-move grundy node lower))))

(defun q1687147-grundy-equation-p
    (ordinal-carrier ordinal-less right-move grundy node)
  (let ((value (q1687147-map-value grundy node)))
    (and
     (q1687147-member-p ordinal-carrier value)
     (q1687147-grundy-value-absent-p
      right-move grundy node value)
     (q1687147-all-lower-grundy-values-attained-p
      ordinal-carrier ordinal-less right-move
      grundy node value))))

(defun-sk q1687147-grundy-semantics-p
    (game-carrier ordinal-carrier ordinal-less right-move grundy)
  (forall (node)
    (implies
     (q1687147-member-p game-carrier node)
     (q1687147-grundy-equation-p
      ordinal-carrier ordinal-less right-move grundy node))))

;; All structures and recursive semantic objects remain universally
;; quantified inside the statement. The hypotheses are precisely their
;; defining equations and the source assumption that the root is impartial.

(defun-sk thousand-theorems-q1687147-sprague-grundy-theorem-statement ()
  (forall
    (game-carrier left-move right-move root
     ordinal-carrier ordinal-less game-le impartial grundy)
    (implies
     (and
      (q1687147-game-p
       game-carrier left-move right-move root)
      (q1687147-well-order-p
       ordinal-carrier ordinal-less)
      (tamep-functionp game-le)
      (tamep-functionp impartial)
      (tamep-functionp grundy)
      (q1687147-game-le-semantics-p
       game-carrier ordinal-carrier left-move right-move
       ordinal-less game-le)
      (q1687147-impartial-semantics-p
       game-carrier left-move right-move game-le impartial)
      (q1687147-grundy-semantics-p
       game-carrier ordinal-carrier ordinal-less right-move grundy)
      (q1687147-member-p impartial root))
     (q1687147-game-equiv-p
      game-le
      (q1687147-nim-position
       (q1687147-map-value grundy root))
      (q1687147-positive-position root)))))

(value-triple :itpeval-statement-checked)
:q
