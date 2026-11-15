;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_a3:
;; a real sequence with three initial ones and consecutive 2-by-2 determinants
;; equal to n factorial is integer-valued. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This conservative generic symbol gives a rational regular Cauchy name for
;; u_n at every natural n. Every real sequence admits such a name, and every
;; name satisfying PUTNAM-2004-A3-REGULAR-REAL-SEQUENCE-NAME-P determines a
;; unique real sequence, so this is equivalent to an arbitrary N -> R input.
(defstub putnam-2004-a3-u-approx (n epsilon) t)

(defun putnam-2004-a3-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun putnam-2004-a3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2004-a3-factorial (- n 1)))))

(defun-sk putnam-2004-a3-regular-real-sequence-name-p ()
  (forall (n epsilon eta)
    (implies
     (and
      (natp n)
      (putnam-2004-a3-positive-rational-p epsilon)
      (putnam-2004-a3-positive-rational-p eta))
     (let ((left
            (putnam-2004-a3-u-approx n epsilon))
           (right
            (putnam-2004-a3-u-approx n eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; For a regular Cauchy name, this universal error bound is equivalent to its
;; represented real value being TARGET.
(defun putnam-2004-a3-equals-rational-at-precision-p
    (n target epsilon)
  (let ((sample
         (putnam-2004-a3-u-approx n epsilon)))
    (and
     (rationalp sample)
     (<= (abs (- sample target))
         epsilon))))

(defun-sk putnam-2004-a3-base-values-p ()
  (forall (epsilon)
    (implies
     (putnam-2004-a3-positive-rational-p epsilon)
     (and
      (putnam-2004-a3-equals-rational-at-precision-p
       0 1 epsilon)
      (putnam-2004-a3-equals-rational-at-precision-p
       1 1 epsilon)
      (putnam-2004-a3-equals-rational-at-precision-p
       2 1 epsilon)))))

(defun putnam-2004-a3-determinant-sample (n precision)
  (-
   (*
    (putnam-2004-a3-u-approx n precision)
    (putnam-2004-a3-u-approx (+ n 3) precision))
   (*
    (putnam-2004-a3-u-approx (+ n 1) precision)
    (putnam-2004-a3-u-approx (+ n 2) precision))))

;; Requiring a precision DELTA no larger than EPSILON prevents a witness from
;; selecting a fixed coarse sample. As EPSILON tends to zero, these samples
;; converge to the exact determinant, so this is equivalent to determinant
;; equality in R.
(defun putnam-2004-a3-determinant-witness-p
    (n epsilon delta)
  (and
   (putnam-2004-a3-positive-rational-p delta)
   (<= delta epsilon)
   (rationalp
    (putnam-2004-a3-u-approx n delta))
   (rationalp
    (putnam-2004-a3-u-approx (+ n 1) delta))
   (rationalp
    (putnam-2004-a3-u-approx (+ n 2) delta))
   (rationalp
    (putnam-2004-a3-u-approx (+ n 3) delta))
   (<=
    (abs
     (-
      (putnam-2004-a3-determinant-sample n delta)
      (putnam-2004-a3-factorial n)))
    epsilon)))

(defun-sk putnam-2004-a3-determinant-witness-exists-p
    (n epsilon)
  (exists (delta)
    (putnam-2004-a3-determinant-witness-p
     n epsilon delta)))

(defun-sk putnam-2004-a3-determinant-recurrence-p ()
  (forall (n epsilon)
    (implies
     (and
      (natp n)
      (putnam-2004-a3-positive-rational-p epsilon))
     (putnam-2004-a3-determinant-witness-exists-p
      n epsilon))))

;; The integer M remains existentially quantified inside the predicate for
;; each n, outside the universal precision quantifier, exactly as in the
;; source conclusion.
(defun-sk putnam-2004-a3-value-equals-integer-p (n m)
  (forall (epsilon)
    (implies
     (putnam-2004-a3-positive-rational-p epsilon)
     (let ((sample
            (putnam-2004-a3-u-approx n epsilon)))
       (and
        (rationalp sample)
        (<= (abs (- sample m))
            epsilon))))))

(defun-sk putnam-2004-a3-integer-value-p (n)
  (exists (m)
    (and
     (integerp m)
     (putnam-2004-a3-value-equals-integer-p n m))))

(defun-sk putnam-2004-a3-all-values-integer-p ()
  (forall (n)
    (implies
     (natp n)
     (putnam-2004-a3-integer-value-p n))))

(defun putnambench-putnam-2004-a3-statement ()
  (implies
   (and
    (putnam-2004-a3-regular-real-sequence-name-p)
    (putnam-2004-a3-base-values-p)
    (putnam-2004-a3-determinant-recurrence-p))
   (putnam-2004-a3-all-values-integer-p)))

(value-triple :itpeval-statement-checked)
:q
