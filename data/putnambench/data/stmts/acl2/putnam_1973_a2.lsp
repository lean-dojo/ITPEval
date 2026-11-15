;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_a2:
;; a periodic signed harmonic series converges exactly when its eight-term
;; sign block contains four plus signs. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun putnam-1973-a2-sign-list-p (signs)
  (if (consp signs)
      (and (or (equal (car signs) 1)
               (equal (car signs) -1))
           (putnam-1973-a2-sign-list-p (cdr signs)))
    (equal signs nil)))

(defun putnam-1973-a2-sign-block-p (signs)
  (and (true-listp signs)
       (equal (len signs) 8)
       (putnam-1973-a2-sign-list-p signs)))

(defun putnam-1973-a2-count-pluses (signs)
  (if (consp signs)
      (+ (if (equal (car signs) 1) 1 0)
         (putnam-1973-a2-count-pluses (cdr signs)))
    0))

;; The nth partial sum is sum_{i=1}^n signs[i mod 8]/i, matching the
;; indexing in the formal sources. Every value is an exact rational.
(defun putnam-1973-a2-partial-sum (signs n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (putnam-1973-a2-partial-sum signs (- n 1))
       (/ (nth (mod n 8) signs) n))))

;; A rational sequence converges in the reals exactly when it is Cauchy.
;; Positive rational tolerances are cofinal among positive real tolerances,
;; so this retains the source's real convergence statement without choosing
;; or externally parameterizing a rational limit.
(defun-sk putnam-1973-a2-cauchy-tail-p
    (signs epsilon cutoff)
  (forall (left-index right-index)
    (implies
     (and (natp cutoff)
          (natp left-index)
          (natp right-index)
          (<= cutoff left-index)
          (<= cutoff right-index))
     (< (abs
         (- (putnam-1973-a2-partial-sum
             signs left-index)
            (putnam-1973-a2-partial-sum
             signs right-index)))
        epsilon))))

(defun-sk putnam-1973-a2-cauchy-cutoff-exists-p
    (signs epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (putnam-1973-a2-cauchy-tail-p
          signs epsilon cutoff))))

(defun-sk putnam-1973-a2-converges-p (signs)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-1973-a2-cauchy-cutoff-exists-p
      signs epsilon))))

(defun-sk putnambench-putnam-1973-a2-statement ()
  (forall (signs)
    (implies
     (putnam-1973-a2-sign-block-p signs)
     (iff (putnam-1973-a2-converges-p signs)
          (equal (putnam-1973-a2-count-pluses signs)
                 4)))))

(value-triple :itpeval-statement-checked)
:q
