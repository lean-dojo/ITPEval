;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_a4:
;; the positive real double series with summand
;; m^2*n/(3^m*(n*3^m+m*3^n)) has value 9/32. This file contains no proof.

(in-package "ACL2")

;; The source series is indexed by positive integers. Its terms are positive,
;; so square finite subsums are cofinal with the source's iterated sum.
(defun putnam-1999-a4-term (m n)
  (if (and (natp m)
           (< 0 m)
           (natp n)
           (< 0 n))
      (/ (* m m n)
         (* (expt 3 m)
            (+ (* n (expt 3 m))
               (* m (expt 3 n)))))
    0))

(defun putnam-1999-a4-row-prefix (m columns)
  (declare (xargs :measure (nfix columns)))
  (if (zp columns)
      0
    (+ (putnam-1999-a4-row-prefix m (- columns 1))
       (putnam-1999-a4-term m columns))))

(defun putnam-1999-a4-rectangle-prefix (rows columns)
  (declare (xargs :measure (nfix rows)))
  (if (zp rows)
      0
    (+ (putnam-1999-a4-rectangle-prefix
        (- rows 1) columns)
       (putnam-1999-a4-row-prefix rows columns))))

(defun putnam-1999-a4-square-prefix (terms)
  (putnam-1999-a4-rectangle-prefix terms terms))

;; Positive rational tolerances are cofinal among positive real tolerances,
;; so convergence of the positive square partial sums states the source
;; iterated-series equality without adding a convergence rate.
(defun-sk putnam-1999-a4-tail-p (epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (< (abs
         (- (putnam-1999-a4-square-prefix terms)
            9/32))
        epsilon))))

(defun-sk putnam-1999-a4-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1999-a4-tail-p epsilon cutoff))))

(defun putnambench-putnam-1999-a4-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1999-a4-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
