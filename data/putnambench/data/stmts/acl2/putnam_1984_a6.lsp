;; Statement-only formalization of PutnamBench corpus artifact putnam_1984_a6:
;; last nonzero digits of factorials at sums of distinct powers of five
;; depend only on the exponent sum, and the resulting sequence has least
;; positive period four from index one. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This conservative symbol represents the arbitrary function f in the
;; source theorem.  PUTNAM-1984-A6-F-SPEC-P below states its full defining
;; hypothesis rather than building any derived formula for its values.
(defstub putnam-1984-a6-f (n) t)

(defun putnam-1984-a6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1984-a6-factorial (- n 1)))))

;; Decimal digits are inspected from right to left.  For positive VALUE,
;; VALUE recursive steps are more than enough to reach its first nonzero
;; digit, while the explicit fuel gives a simple total ACL2 definition.
(defun putnam-1984-a6-last-nonzero-digit-aux (value fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      0
    (let ((digit (mod value 10)))
      (if (equal digit 0)
          (putnam-1984-a6-last-nonzero-digit-aux
           (floor value 10)
           (- fuel 1))
        digit))))

(defun putnam-1984-a6-last-nonzero-digit (value)
  (putnam-1984-a6-last-nonzero-digit-aux value value))

(defun-sk putnam-1984-a6-f-spec-p ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (putnam-1984-a6-f n)
      (putnam-1984-a6-last-nonzero-digit
       (putnam-1984-a6-factorial n))))))

(defun putnam-1984-a6-natural-list-p (values)
  (if (consp values)
      (and
       (natp (car values))
       (putnam-1984-a6-natural-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1984-a6-sum-exponents (exponents)
  (if (consp exponents)
      (+ (car exponents)
         (putnam-1984-a6-sum-exponents (cdr exponents)))
    0))

(defun putnam-1984-a6-sum-powers-five (exponents)
  (if (consp exponents)
      (+ (expt 5 (car exponents))
         (putnam-1984-a6-sum-powers-five (cdr exponents)))
    0))

(defun putnam-1984-a6-g-value (g s)
  (apply$ g (list s)))

(defun-sk putnam-1984-a6-g-natural-valued-p (g)
  (forall (s)
    (implies
     (natp s)
     (natp (putnam-1984-a6-g-value g s)))))

;; A nonempty duplicate-free natural list is an enumeration of exactly one
;; finite injective family Fin k -> Nat with k > 0, and conversely every such
;; family has such a list enumeration.
(defun-sk putnam-1984-a6-dependence-p (g)
  (forall (exponents)
    (implies
     (and
      (true-listp exponents)
      (consp exponents)
      (putnam-1984-a6-natural-list-p exponents)
      (no-duplicatesp-equal exponents))
     (equal
      (putnam-1984-a6-f
       (putnam-1984-a6-sum-powers-five exponents))
      (putnam-1984-a6-g-value
       g
       (putnam-1984-a6-sum-exponents exponents))))))

(defun-sk putnam-1984-a6-periodic-from-one-p (g period)
  (forall (s)
    (implies
     (and
      (natp s)
      (<= 1 s))
     (equal
      (putnam-1984-a6-g-value g s)
      (putnam-1984-a6-g-value g (+ s period))))))

(defun-sk putnam-1984-a6-four-is-least-positive-period-p (g)
  (forall (period)
    (implies
     (and
      (natp period)
      (< 0 period)
      (putnam-1984-a6-periodic-from-one-p g period))
     (<= 4 period))))

(defun putnam-1984-a6-solution-p (g)
  (and
   (putnam-1984-a6-periodic-from-one-p g 4)
   (putnam-1984-a6-four-is-least-positive-period-p g)))

(defun-sk putnam-1984-a6-witness-exists-p ()
  (exists (g)
    (and
     (tamep-functionp g)
     (putnam-1984-a6-g-natural-valued-p g)
     (putnam-1984-a6-dependence-p g)
     (putnam-1984-a6-solution-p g))))

(defun putnambench-putnam-1984-a6-statement ()
  (implies
   (putnam-1984-a6-f-spec-p)
   (putnam-1984-a6-witness-exists-p)))

(value-triple :itpeval-statement-checked)
:q
