;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_b3:
;; characterize the initial real value a for which every term of the real
;; sequence u, defined by u(0) = a and u(n+1) = 2*u(n) - n^2, is positive.
;; This file contains no proof.

(in-package "ACL2")

;; An arbitrary real number is represented exactly by a regular rational
;; Cauchy name.  At positive rational precision epsilon, the name supplies a
;; rational approximation whose distance from the represented real is at
;; most epsilon.  The regularity condition below is an exact, bidirectional
;; presentation of the completion of the rationals: every such name
;; determines one real number, and every real number admits such a name.
(defstub p80b3-a-approx (a precision) t)

;; Likewise, SEQUENCE is an exact name for an arbitrary function N -> R:
;; p80b3-u-approx supplies a regular rational Cauchy name independently at
;; every natural-number index.  Every real-valued sequence admits such a
;; pointwise name, so this representation does not restrict the source domain.
(defstub p80b3-u-approx (sequence index precision) t)

(defun p80b3-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun-sk p80b3-real-name-p (a)
  (forall
   (epsilon eta)
   (implies
    (and (p80b3-positive-rational-p epsilon)
         (p80b3-positive-rational-p eta))
    (let ((left (p80b3-a-approx a epsilon))
          (right (p80b3-a-approx a eta)))
      (and (rationalp left)
           (rationalp right)
           (<= (abs (- left right))
               (+ epsilon eta)))))))

(defun-sk p80b3-sequence-name-p (sequence)
  (forall
   (index epsilon eta)
   (implies
    (and (natp index)
         (p80b3-positive-rational-p epsilon)
         (p80b3-positive-rational-p eta))
    (let ((left (p80b3-u-approx sequence index epsilon))
          (right (p80b3-u-approx sequence index eta)))
      (and (rationalp left)
           (rationalp right)
           (<= (abs (- left right))
               (+ epsilon eta)))))))

;; For regular names, two represented reals are equal exactly when their
;; same-precision approximations differ by at most 2*epsilon at every
;; positive rational epsilon.  Thus this predicate states u(0) = a.
(defun-sk p80b3-initial-value-p (a sequence)
  (forall
   (epsilon)
   (implies
    (p80b3-positive-rational-p epsilon)
    (let ((a-epsilon (p80b3-a-approx a epsilon))
          (u0-epsilon (p80b3-u-approx sequence 0 epsilon)))
      (and (rationalp a-epsilon)
           (rationalp u0-epsilon)
           (<= (abs (- u0-epsilon a-epsilon))
               (* 2 epsilon)))))))

;; The right-hand approximation uses precision epsilon/2 before multiplication
;; by 2, so it approximates 2*u(n)-n^2 within epsilon.  Comparing it with an
;; epsilon-approximation of u(n+1) using the bound 2*epsilon is therefore
;; exactly equivalent, for regular names, to
;;     u(n+1) = 2*u(n) - n^2
;; at every natural-number index.
(defun-sk p80b3-recurrence-p (sequence)
  (forall
   (index epsilon)
   (implies
    (and (natp index)
         (p80b3-positive-rational-p epsilon))
    (let* ((next-value
            (p80b3-u-approx sequence (+ 1 index) epsilon))
           (current-value
            (p80b3-u-approx sequence index (/ epsilon 2)))
           (right-hand-side
            (- (* 2 current-value)
               (* index index))))
      (and (rationalp next-value)
           (rationalp current-value)
           (<= (abs (- next-value right-hand-side))
               (* 2 epsilon)))))))

;; A represented real x is strictly positive exactly when there is a positive
;; rational lower bound L such that L <= x_epsilon + epsilon at every positive
;; rational precision.  The existential margin remains internal to positivity.
(defun-sk p80b3-positive-margin-p (sequence index lower)
  (forall
   (epsilon)
   (implies
    (p80b3-positive-rational-p epsilon)
    (let ((value (p80b3-u-approx sequence index epsilon)))
      (and (rationalp value)
           (<= lower (+ value epsilon)))))))

(defun-sk p80b3-positive-at-index-p (sequence index)
  (exists
   (lower)
   (and (p80b3-positive-rational-p lower)
        (p80b3-positive-margin-p sequence index lower))))

(defun-sk p80b3-positive-at-every-index-p (sequence)
  (forall
   (index)
   (implies
    (natp index)
    (p80b3-positive-at-index-p sequence index))))

;; For a regular name, the represented real is at least 3 exactly when every
;; epsilon-approximation plus its error allowance is at least 3.
(defun-sk p80b3-at-least-three-p (a)
  (forall
   (epsilon)
   (implies
    (p80b3-positive-rational-p epsilon)
    (let ((value (p80b3-a-approx a epsilon)))
      (and (rationalp value)
           (<= 3 (+ value epsilon)))))))

(defun putnambench-putnam-1980-b3-statement (a sequence)
  (implies
   (and (p80b3-real-name-p a)
        (p80b3-sequence-name-p sequence)
        (p80b3-initial-value-p a sequence)
        (p80b3-recurrence-p sequence))
   (iff (p80b3-positive-at-every-index-p sequence)
        (p80b3-at-least-three-p a))))

(value-triple :itpeval-statement-checked)
:q
