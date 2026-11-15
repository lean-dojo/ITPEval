;; Statement-only formalization of PutnamBench artifact putnam_1965_b2:
;; equality of the sums of squared win and loss counts in a finite
;; round-robin tournament. This file contains no proof.

(in-package "ACL2")

;; The source finite player type is represented by the canonical carrier
;; 0,...,n-1. Any n-element type is bijective with this carrier, and transport
;; along such a bijection preserves the tournament axioms and both sums.
;; WON is an ACL2 function object evaluated by APPLY$, not a finite table.

(defun putnam-1965-b2-won-value (won player opponent)
  (apply$ won (list player opponent)))

(defun putnam-1965-b2-boolean-row-p
    (won player remaining-opponents)
  (declare (xargs :measure (nfix remaining-opponents)))
  (if (zp remaining-opponents)
      t
    (let ((opponent (- remaining-opponents 1)))
      (and
       (booleanp
        (putnam-1965-b2-won-value won player opponent))
       (putnam-1965-b2-boolean-row-p
        won player opponent)))))

(defun putnam-1965-b2-boolean-matrix-p
    (won remaining-players n)
  (declare (xargs :measure (nfix remaining-players)))
  (if (zp remaining-players)
      t
    (let ((player (- remaining-players 1)))
      (and
       (putnam-1965-b2-boolean-row-p won player n)
       (putnam-1965-b2-boolean-matrix-p
        won player n)))))

(defun putnam-1965-b2-irreflexive-p
    (won remaining-players)
  (declare (xargs :measure (nfix remaining-players)))
  (if (zp remaining-players)
      t
    (let ((player (- remaining-players 1)))
      (and
       (equal
        (putnam-1965-b2-won-value won player player)
        nil)
       (putnam-1965-b2-irreflexive-p won player)))))

(defun putnam-1965-b2-antisymmetric-row-p
    (won player remaining-opponents)
  (declare (xargs :measure (nfix remaining-opponents)))
  (if (zp remaining-opponents)
      t
    (let ((opponent (- remaining-opponents 1)))
      (and
       (or
        (equal player opponent)
        (equal
         (putnam-1965-b2-won-value won player opponent)
         (not
          (putnam-1965-b2-won-value
           won opponent player))))
       (putnam-1965-b2-antisymmetric-row-p
        won player opponent)))))

(defun putnam-1965-b2-antisymmetric-p
    (won remaining-players n)
  (declare (xargs :measure (nfix remaining-players)))
  (if (zp remaining-players)
      t
    (let ((player (- remaining-players 1)))
      (and
       (putnam-1965-b2-antisymmetric-row-p
        won player n)
       (putnam-1965-b2-antisymmetric-p
        won player n)))))

(defun putnam-1965-b2-win-count
    (won player remaining-opponents)
  (declare (xargs :measure (nfix remaining-opponents)))
  (if (zp remaining-opponents)
      0
    (let ((opponent (- remaining-opponents 1)))
      (+
       (if (putnam-1965-b2-won-value
            won player opponent)
           1
         0)
       (putnam-1965-b2-win-count
        won player opponent)))))

(defun putnam-1965-b2-sum-win-squares
    (won remaining-players n)
  (declare (xargs :measure (nfix remaining-players)))
  (if (zp remaining-players)
      0
    (let* ((player (- remaining-players 1))
           (wins
            (putnam-1965-b2-win-count won player n)))
      (+
       (* wins wins)
       (putnam-1965-b2-sum-win-squares
        won player n)))))

(defun putnam-1965-b2-sum-loss-squares
    (won remaining-players n)
  (declare (xargs :measure (nfix remaining-players)))
  (if (zp remaining-players)
      0
    (let* ((player (- remaining-players 1))
           (wins
            (putnam-1965-b2-win-count won player n))
           (losses (- (- n 1) wins)))
      (+
       (* losses losses)
       (putnam-1965-b2-sum-loss-squares
        won player n)))))

;; W and L from the source are definitionally eliminated by substituting
;; w(r) = sum_j if won(r,j) then 1 else 0 and l(r) = n - 1 - w(r).
(defun putnambench-putnam-1965-b2-statement (n won)
  (implies
   (and
    (natp n)
    (< 1 n)
    (putnam-1965-b2-boolean-matrix-p won n n)
    (putnam-1965-b2-irreflexive-p won n)
    (putnam-1965-b2-antisymmetric-p won n n))
   (equal
    (putnam-1965-b2-sum-win-squares won n n)
    (putnam-1965-b2-sum-loss-squares won n n))))

(value-triple :itpeval-statement-checked)
:q
