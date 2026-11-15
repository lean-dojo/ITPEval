;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_a5:
;; the greatest number of uncovered squares that Alice can guarantee in the
;; 2022-square adjacent-domino game is 290. This file contains no proof.

(in-package "ACL2")

;; Natural-number bitmasks below 2^2022 are in bijection with subsets of
;; Fin 2022: bit i is set exactly when square i is covered. A strategy is a
;; finite association list from board masks to board masks. Because the board
;; domain is finite, every source strategy has such a table and every table
;; denotes a source strategy through deterministic lookup.
(defun putnam-2022-a5-valid-board-p (board)
  (and
   (natp board)
   (< board (expt 2 2022))))

(defun putnam-2022-a5-coveredp (board square)
  (if (and (natp board)
           (natp square))
      (logbitp square board)
    nil))

(defun putnam-2022-a5-legal-placement-p (board left)
  (and
   (natp board)
   (natp left)
   (< left 2021)
   (not (putnam-2022-a5-coveredp board left))
   (not (putnam-2022-a5-coveredp board (+ left 1)))))

(defun putnam-2022-a5-place-tile (board left)
  (logior
   (nfix board)
   (* 3 (expt 2 (nfix left)))))

(defun putnam-2022-a5-uncovered-from (board square)
  (declare (xargs :measure (nfix (- 2022 square))))
  (if (and (natp square)
           (< square 2022))
      (+ (if (putnam-2022-a5-coveredp board square)
             0
           1)
         (putnam-2022-a5-uncovered-from
          board (+ square 1)))
    0))

(defun putnam-2022-a5-no-placement-from-p (board left)
  (declare (xargs :measure (nfix (- 2021 left))))
  (if (and (natp left)
           (< left 2021))
      (and
       (not (putnam-2022-a5-legal-placement-p board left))
       (putnam-2022-a5-no-placement-from-p board (+ left 1)))
    t))

(defun putnam-2022-a5-placement-move-from-p (before after left)
  (declare (xargs :measure (nfix (- 2021 left))))
  (if (and (natp left)
           (< left 2021))
      (or
       (and
        (putnam-2022-a5-legal-placement-p before left)
        (equal
         after
         (putnam-2022-a5-place-tile before left)))
       (putnam-2022-a5-placement-move-from-p
        before after (+ left 1)))
    nil))

;; This is the source IsValidMove relation: a terminal board may repeat, and
;; otherwise one legal adjacent pair is added.
(defun putnam-2022-a5-valid-move-p (before after)
  (and
   (putnam-2022-a5-valid-board-p before)
   (putnam-2022-a5-valid-board-p after)
   (or
    (and
     (equal before after)
     (putnam-2022-a5-no-placement-from-p before 0))
    (putnam-2022-a5-placement-move-from-p before after 0))))

(defun putnam-2022-a5-valid-game-chain-p (game)
  (if (or (endp game)
          (endp (cdr game)))
      t
    (and
     (putnam-2022-a5-valid-move-p (car game) (cadr game))
     (putnam-2022-a5-valid-game-chain-p (cdr game)))))

;; Nonempty, starts at the empty board, and satisfies Chain' IsValidMove.
(defun putnam-2022-a5-valid-game-p (game)
  (and
   (true-listp game)
   (consp game)
   (equal (car game) 0)
   (putnam-2022-a5-valid-game-chain-p game)))

(defun putnam-2022-a5-strategy-move (strategy board)
  (let ((entry (assoc-equal board strategy)))
    (if entry
        (cdr entry)
      nil)))

;; DEFUN-SK preserves the source's universal quantifier over every board.
(defun-sk putnam-2022-a5-valid-strategy-p (strategy)
  (forall (board)
    (implies
     (putnam-2022-a5-valid-board-p board)
     (putnam-2022-a5-valid-move-p
      board
      (putnam-2022-a5-strategy-move strategy board)))))

(defun putnam-2022-a5-conforms-from-p (game strategy index)
  (if (or (endp game)
          (endp (cdr game)))
      t
    (and
     (if (equal (mod (nfix index) 2) 0)
         (equal
          (cadr game)
          (putnam-2022-a5-strategy-move
           strategy (car game)))
       t)
     (putnam-2022-a5-conforms-from-p
      (cdr game) strategy (+ 1 (nfix index))))))

(defun putnam-2022-a5-conforms-to-strategy-p (game strategy)
  (putnam-2022-a5-conforms-from-p game strategy 0))

(defun putnam-2022-a5-last-board (game)
  (if (or (endp game)
          (endp (cdr game)))
      (if (consp game) (car game) 0)
    (putnam-2022-a5-last-board (cdr game))))

;; This universal quantifier is the source's "for every valid game conforming
;; to Alice's strategy" clause. The append decomposition is equivalent to
;; selecting the last board because every valid game is a nonempty true list.
(defun-sk putnam-2022-a5-strategy-guarantees-p (n strategy)
  (forall (game)
    (implies
     (and
      (putnam-2022-a5-valid-game-p game)
      (putnam-2022-a5-conforms-to-strategy-p game strategy))
     (<=
      (nfix n)
      (putnam-2022-a5-uncovered-from
       (putnam-2022-a5-last-board game)
       0)))))

;; Quantifying over finite strategy tables is exact because the source board
;; domain has 2^2022 elements. No strategy witness or game is hardcoded.
(defun-sk putnam-2022-a5-guaranteed-p (n)
  (exists (strategy)
    (and
     (natp n)
     (alistp strategy)
     (putnam-2022-a5-valid-strategy-p strategy)
     (putnam-2022-a5-strategy-guarantees-p n strategy))))

(defun-sk putnam-2022-a5-solution-upper-bound-p ()
  (forall (n)
    (implies
     (putnam-2022-a5-guaranteed-p n)
     (<= n 290))))

;; IsGreatest is unfolded as membership plus the universal upper-bound clause.
(defun putnambench-putnam-2022-a5-statement ()
  (and
   (putnam-2022-a5-guaranteed-p 290)
   (putnam-2022-a5-solution-upper-bound-p)))

(value-triple :itpeval-statement-checked)
:q
