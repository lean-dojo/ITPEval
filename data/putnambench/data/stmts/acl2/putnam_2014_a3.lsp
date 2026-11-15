;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_a3:
;; the finite products associated with a_0 = 5/2 and
;; a_k = a_(k-1)^2 - 2 converge to 3/7. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The recurrence uniquely determines the source real sequence, and every
;; value is rational. Thus this exact recursive definition eliminates the
;; arbitrary sequence parameter without restricting the source statement.
(defun putnam-2014-a3-sequence-value (index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      5/2
    (let ((previous
           (putnam-2014-a3-sequence-value (- index 1))))
      (- (* previous previous) 2))))

;; Product over 0 <= k < terms, including the empty product at terms = 0.
(defun putnam-2014-a3-partial-product (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      1
    (* (putnam-2014-a3-partial-product (- terms 1))
       (- 1
          (/ 1
             (putnam-2014-a3-sequence-value
              (- terms 1)))))))

(defun-sk putnam-2014-a3-tail-p (epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (<
      (abs
       (- (putnam-2014-a3-partial-product terms)
          3/7))
      epsilon))))

(defun-sk putnam-2014-a3-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2014-a3-tail-p epsilon cutoff))))

;; Because all partial products and the proposed limit are rational,
;; quantifying over positive rational epsilons is equivalent to the usual
;; real epsilon definition of convergence.
(defun-sk putnam-2014-a3-converges-p ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2014-a3-cutoff-exists-p epsilon))))

(defun putnambench-putnam-2014-a3-statement ()
  (putnam-2014-a3-converges-p))

(value-triple :itpeval-statement-checked)
:q
