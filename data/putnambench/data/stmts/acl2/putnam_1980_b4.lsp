;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_b4:
;; 1,066 subsets of a finite set, each containing more than half its elements,
;; have a 10-element subset meeting every one. This file contains no proof.

(in-package "ACL2")

;; A finite set is represented by a duplicate-free true list. The order of
;; FAMILY represents the finite index set, and each entry is a duplicate-free
;; enumeration of the corresponding subset. Choosing enumerations gives this
;; representation for every source X and A, while forgetting list order and
;; reading positions as indices recovers them. Thus the representation is
;; bidirectional and does not restrict the element type or the finite sets.

(defun putnam-1980-b4-subsetp-equal (subset carrier)
  (if (consp subset)
      (and
       (member-equal (car subset) carrier)
       (putnam-1980-b4-subsetp-equal
        (cdr subset) carrier))
    (equal subset nil)))

(defun putnam-1980-b4-family-hypotheses-p
    (family carrier)
  (if (consp family)
      (and
       (true-listp (car family))
       (no-duplicatesp-equal (car family))
       (putnam-1980-b4-subsetp-equal
        (car family) carrier)
       (< (len carrier) (* 2 (len (car family))))
       (putnam-1980-b4-family-hypotheses-p
        (cdr family) carrier))
    (equal family nil)))

(defun putnam-1980-b4-intersects-p (left right)
  (if (consp left)
      (or
       (member-equal (car left) right)
       (putnam-1980-b4-intersects-p
        (cdr left) right))
    nil))

(defun putnam-1980-b4-meets-every-p
    (candidate family)
  (if (consp family)
      (and
       (putnam-1980-b4-intersects-p
        candidate (car family))
       (putnam-1980-b4-meets-every-p
        candidate (cdr family)))
    (equal family nil)))

;; This exhaustive recursion ranges over every subset of CARRIER. CHOSEN is
;; constructed only from carrier elements, so a successful leaf is exactly an
;; internal 10-element subset witness meeting every member of FAMILY.
(defun putnam-1980-b4-transversal-exists-p
    (remaining chosen family)
  (declare (xargs :measure (len remaining)))
  (if (consp remaining)
      (or
       (putnam-1980-b4-transversal-exists-p
        (cdr remaining)
        (cons (car remaining) chosen)
        family)
       (putnam-1980-b4-transversal-exists-p
        (cdr remaining)
        chosen
        family))
    (and
     (equal remaining nil)
     (equal (len chosen) 10)
     (putnam-1980-b4-meets-every-p
      chosen family))))

(defun putnambench-putnam-1980-b4-statement
    (carrier family)
  (implies
   (and
    (true-listp carrier)
    (no-duplicatesp-equal carrier)
    (<= 10 (len carrier))
    (true-listp family)
    (equal (len family) 1066)
    (putnam-1980-b4-family-hypotheses-p
     family carrier))
   (putnam-1980-b4-transversal-exists-p
    carrier nil family)))

(value-triple :itpeval-statement-checked)
:q
