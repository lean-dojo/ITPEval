;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_b3:
;; every normalized modular real valuation on the specified finite lattice of
;; subsets is a sum of element weights. This file contains no proof.

(in-package "ACL2")

;; An n-bit natural is the characteristic function of a subset of Fin n.
;; Duplicate-free lists therefore represent the source finsets exactly.

(defun putnam-2013-b3-mask-union (left right width)
  (declare (xargs :measure (nfix width)))
  (if (zp width)
      0
    (+ (if (or (equal (mod left 2) 1)
               (equal (mod right 2) 1))
           1
         0)
       (* 2
          (putnam-2013-b3-mask-union
           (floor left 2)
           (floor right 2)
           (- width 1))))))

(defun putnam-2013-b3-mask-intersection (left right width)
  (declare (xargs :measure (nfix width)))
  (if (zp width)
      0
    (+ (if (and (equal (mod left 2) 1)
                (equal (mod right 2) 1))
           1
         0)
       (* 2
          (putnam-2013-b3-mask-intersection
           (floor left 2)
           (floor right 2)
           (- width 1))))))

(defun putnam-2013-b3-mask-card (mask width)
  (declare (xargs :measure (nfix width)))
  (if (zp width)
      0
    (+ (if (equal (mod mask 2) 1) 1 0)
       (putnam-2013-b3-mask-card
        (floor mask 2)
        (- width 1)))))

(defun putnam-2013-b3-valid-masks-p (family bound)
  (if (consp family)
      (and (natp (car family))
           (< (car family) bound)
           (putnam-2013-b3-valid-masks-p
            (cdr family)
            bound))
    (equal family nil)))

(defun putnam-2013-b3-closure-row-p
    (left rights family width)
  (if (consp rights)
      (and
       (member-equal
        (putnam-2013-b3-mask-union
         left (car rights) width)
        family)
       (member-equal
        (putnam-2013-b3-mask-intersection
         left (car rights) width)
        family)
       (putnam-2013-b3-closure-row-p
        left (cdr rights) family width))
    (equal rights nil)))

(defun putnam-2013-b3-closed-family-p
    (remaining family width)
  (if (consp remaining)
      (and
       (putnam-2013-b3-closure-row-p
        (car remaining) family family width)
       (putnam-2013-b3-closed-family-p
        (cdr remaining) family width))
    (equal remaining nil)))

(defun putnam-2013-b3-lower-cover-exists-p
    (set family width)
  (if (consp family)
      (let ((candidate (car family)))
        (or
         (and
          (not (equal candidate set))
          (equal
           (putnam-2013-b3-mask-intersection
            candidate set width)
           candidate)
          (equal
           (+ (putnam-2013-b3-mask-card
               candidate width)
              1)
           (putnam-2013-b3-mask-card
            set width)))
         (putnam-2013-b3-lower-cover-exists-p
          set (cdr family) width)))
    nil))

(defun putnam-2013-b3-graded-family-p
    (remaining family width)
  (if (consp remaining)
      (and
       (or
        (equal (car remaining) 0)
        (putnam-2013-b3-lower-cover-exists-p
         (car remaining) family width))
       (putnam-2013-b3-graded-family-p
        (cdr remaining) family width))
    (equal remaining nil)))

(defun putnam-2013-b3-rational-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (putnam-2013-b3-rational-list-p
            (cdr values)))
    (equal values nil)))

(defun putnam-2013-b3-valuation-row-p
    (left rights values width)
  (if (consp rights)
      (let* ((right (car rights))
             (union
              (putnam-2013-b3-mask-union
               left right width))
             (intersection
              (putnam-2013-b3-mask-intersection
               left right width)))
        (and
         (equal
          (nth union values)
          (-
           (+ (nth left values)
              (nth right values))
           (nth intersection values)))
         (putnam-2013-b3-valuation-row-p
          left (cdr rights) values width)))
    (equal rights nil)))

(defun putnam-2013-b3-valuation-p
    (remaining family values width)
  (if (consp remaining)
      (and
       (putnam-2013-b3-valuation-row-p
        (car remaining) family values width)
       (putnam-2013-b3-valuation-p
        (cdr remaining) family values width))
    (equal remaining nil)))

;; For a fixed family, the desired weights solve the incidence system whose
;; row for S has coefficient 1 at exactly the elements of S and right-hand
;; side f(S). A rational matrix system is solvable exactly when its coefficient
;; and augmented ranks agree.

(defun putnam-2013-b3-incidence-row (mask width)
  (declare (xargs :measure (nfix width)))
  (if (zp width)
      nil
    (cons
     (if (equal (mod mask 2) 1) 1 0)
     (putnam-2013-b3-incidence-row
      (floor mask 2)
      (- width 1)))))

(defun putnam-2013-b3-coefficient-rows (family width)
  (if (consp family)
      (cons
       (putnam-2013-b3-incidence-row
        (car family) width)
       (putnam-2013-b3-coefficient-rows
        (cdr family) width))
    nil))

(defun putnam-2013-b3-augmented-rows
    (family values width)
  (if (consp family)
      (cons
       (append
        (putnam-2013-b3-incidence-row
         (car family) width)
        (list (nth (car family) values)))
       (putnam-2013-b3-augmented-rows
        (cdr family) values width))
    nil))

(defun putnam-2013-b3-first-pivot-row (rows column)
  (if (consp rows)
      (if (equal (nth column (car rows)) 0)
          (putnam-2013-b3-first-pivot-row
           (cdr rows) column)
        (car rows))
    nil))

(defun putnam-2013-b3-remove-first-row (row rows)
  (if (consp rows)
      (if (equal row (car rows))
          (cdr rows)
        (cons
         (car rows)
         (putnam-2013-b3-remove-first-row
          row (cdr rows))))
    nil))

(defun putnam-2013-b3-eliminate-vector
    (row pivot factor)
  (if (and (consp row)
           (consp pivot))
      (cons
       (- (car row)
          (* factor (car pivot)))
       (putnam-2013-b3-eliminate-vector
        (cdr row) (cdr pivot) factor))
    nil))

(defun putnam-2013-b3-eliminate-rows
    (rows pivot column pivot-entry)
  (if (consp rows)
      (cons
       (putnam-2013-b3-eliminate-vector
        (car rows)
        pivot
        (/ (nth column (car rows))
           pivot-entry))
       (putnam-2013-b3-eliminate-rows
        (cdr rows)
        pivot
        column
        pivot-entry))
    nil))

(defun putnam-2013-b3-row-rank-aux
    (rows column columns-left)
  (declare (xargs :measure (nfix columns-left)))
  (if (or (zp columns-left)
          (endp rows))
      0
    (let ((pivot
           (putnam-2013-b3-first-pivot-row
            rows column)))
      (if (not pivot)
          (putnam-2013-b3-row-rank-aux
           rows
           (+ column 1)
           (- columns-left 1))
        (+ 1
           (putnam-2013-b3-row-rank-aux
            (putnam-2013-b3-eliminate-rows
             (putnam-2013-b3-remove-first-row
              pivot rows)
             pivot
             column
             (nth column pivot))
            (+ column 1)
            (- columns-left 1)))))))

(defun putnam-2013-b3-row-rank (rows width)
  (putnam-2013-b3-row-rank-aux rows 0 width))

(defun putnam-2013-b3-weight-representation-exists-p
    (family values width)
  (equal
   (putnam-2013-b3-row-rank
    (putnam-2013-b3-coefficient-rows
     family width)
    width)
   (putnam-2013-b3-row-rank
    (putnam-2013-b3-augmented-rows
     family values width)
    (+ width 1))))

;; The source quantifies over real f and real weights. For each fixed finite
;; family, both its valuation hypotheses and its incidence conclusion are
;; linear systems with integer coefficients. A real counterexample exists iff
;; the corresponding rational subspace inclusion fails, and rational Gaussian
;; elimination then supplies a rational counterexample. Conversely every
;; rational counterexample is real. Thus the universal rational predicate below
;; is bidirectionally equivalent to the source's universal real proposition;
;; it does not narrow the theorem to a proper class of cases.

(defun putnambench-putnam-2013-b3-statement
    (n family values)
  (implies
   (and
    (natp n)
    (true-listp family)
    (consp family)
    (no-duplicatesp-equal family)
    (putnam-2013-b3-valid-masks-p
     family (expt 2 n))
    (putnam-2013-b3-closed-family-p
     family family n)
    (putnam-2013-b3-graded-family-p
     family family n)
    (true-listp values)
    (equal (len values) (expt 2 n))
    (putnam-2013-b3-rational-list-p values)
    (equal (nth 0 values) 0)
    (putnam-2013-b3-valuation-p
     family family values n))
   (putnam-2013-b3-weight-representation-exists-p
    family values n)))

(value-triple :itpeval-statement-checked)
:q
