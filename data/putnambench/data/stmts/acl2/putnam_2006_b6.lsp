;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_b6:
;; the asymptotic limit of a positive real sequence defined by reciprocal
;; positive kth-root increments is ((k+1)/k)^k. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This conservative generic symbol supplies a rational regular Cauchy name
;; for a_n at every natural n. It is an arbitrary function symbol, not a
;; rational-valued sequence or a finite table. Every real sequence admits such
;; a name, and every name satisfying P06B6-REGULAR-NAME-P determines a unique
;; real sequence.
;;
;; If d_n = a_(n+1)-a_n, positivity and
;;
;;   a_n * d_n^k = 1
;;
;; are equivalent to d_n being the positive reciprocal kth root of a_n. The
;; recurrence predicate states this equivalent relation through Cauchy-name
;; approximations. All universal and existential scopes, including the limit
;; cutoff, are internal DEFUN-SK quantifiers.

(defstub p06b6-a-approx (n epsilon) t)

(defun p06b6-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun p06b6-minimum (left right)
  (if (< left right) left right))

(defun p06b6-value-bound (value-at-one)
  (+ 2 (abs value-at-one)))

(defun p06b6-solution (k)
  (expt (/ (+ k 1) k) k))

(defun-sk p06b6-regular-name-p ()
  (forall (n epsilon eta)
    (implies
     (and
      (natp n)
      (p06b6-positive-rational-p epsilon)
      (p06b6-positive-rational-p eta))
     (let ((at-epsilon
            (p06b6-a-approx n epsilon))
           (at-eta
            (p06b6-a-approx n eta)))
       (and
        (rationalp at-epsilon)
        (rationalp at-eta)
        (<=
         (abs (- at-epsilon at-eta))
         (+ epsilon eta)))))))

;; A positive rational lower margin valid at every precision is equivalent to
;; positivity of the represented initial real.

(defun-sk p06b6-initial-margin-p (margin)
  (forall (epsilon)
    (implies
     (p06b6-positive-rational-p epsilon)
     (let ((value
            (p06b6-a-approx 0 epsilon)))
       (and
        (rationalp value)
        (<= margin (+ value epsilon)))))))

(defun-sk p06b6-initial-positive-p ()
  (exists (margin)
    (and
     (p06b6-positive-rational-p margin)
     (p06b6-initial-margin-p margin))))

;; DELTA is small enough that regular-name errors in
;; a_n*(a_(n+1)-a_n)^k contribute at most half the requested tolerance.

(defun p06b6-recurrence-delta (n k epsilon)
  (let* ((current-at-one
          (p06b6-a-approx n 1))
         (next-at-one
          (p06b6-a-approx (+ n 1) 1))
         (current-bound
          (p06b6-value-bound current-at-one))
         (next-bound
          (p06b6-value-bound next-at-one))
         (difference-bound
          (+ 2 current-bound next-bound))
         (power-error-scale
          (+
           1
           (expt difference-bound k)
           (*
            2
            current-bound
            k
            (expt difference-bound (- k 1))))))
    (p06b6-minimum
     1
     (/ epsilon (* 2 power-error-scale)))))

(defun-sk p06b6-recurrence-p (k)
  (forall (n epsilon)
    (implies
     (and
      (natp n)
      (p06b6-positive-rational-p epsilon))
     (let* ((delta
             (p06b6-recurrence-delta
              n k epsilon))
            (current-at-one
             (p06b6-a-approx n 1))
            (next-at-one
             (p06b6-a-approx (+ n 1) 1))
            (current
             (p06b6-a-approx n delta))
            (next
             (p06b6-a-approx (+ n 1) delta))
            (difference (- next current))
            (residual
             (abs
              (-
               (* current
                  (expt difference k))
               1))))
       (and
        (p06b6-positive-rational-p delta)
        (rationalp current-at-one)
        (rationalp next-at-one)
        (rationalp current)
        (rationalp next)
        (<= 0 (+ difference (* 2 delta)))
        (<= residual epsilon))))))

;; The one-quarter name-error allowance and three-quarter comparison margin
;; give an epsilon-equivalent formulation of the usual real limit.

(defun p06b6-limit-delta (n k epsilon)
  (let* ((value-at-one
          (p06b6-a-approx n 1))
         (value-bound
          (+ 1 (p06b6-value-bound value-at-one)))
         (power-error-scale
          (+
           1
           (* (+ k 1)
              (expt value-bound k)))))
    (p06b6-minimum
     1
     (/ epsilon (* 4 power-error-scale)))))

(defun-sk p06b6-limit-tail-p
    (k epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (let* ((delta
             (p06b6-limit-delta n k epsilon))
            (value-at-one
             (p06b6-a-approx n 1))
            (value
             (p06b6-a-approx n delta))
            (quotient
             (/
              (expt value (+ k 1))
              (expt n k)))
            (distance
             (abs
              (- quotient
                 (p06b6-solution k)))))
       (and
        (p06b6-positive-rational-p delta)
        (rationalp value-at-one)
        (rationalp value)
        (< distance (* 3/4 epsilon)))))))

(defun-sk p06b6-limit-cutoff-exists-p
    (k epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p06b6-limit-tail-p
      k epsilon cutoff))))

(defun-sk p06b6-limit-p (k)
  (forall (epsilon)
    (implies
     (p06b6-positive-rational-p epsilon)
     (p06b6-limit-cutoff-exists-p
      k epsilon))))

(defun-sk putnambench-putnam-2006-b6-statement ()
  (forall (k)
    (implies
     (and
      (natp k)
      (< 1 k)
      (p06b6-regular-name-p)
      (p06b6-initial-positive-p)
      (p06b6-recurrence-p k))
     (p06b6-limit-p k))))

(value-triple :itpeval-statement-checked)
:q
