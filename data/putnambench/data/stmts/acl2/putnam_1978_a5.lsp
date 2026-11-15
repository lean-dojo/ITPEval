;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_a5:
;; for a nonempty finite family of real numbers in (0, pi), the product of
;; sin(x)/x is at most the corresponding power at their arithmetic mean.
;; This file contains no proof.

(in-package "ACL2")

;; ACL2's exact rationals give a dense presentation of this universal real
;; inequality. For each fixed positive family size, the defect between the two
;; sides is continuous on (0,pi)^n. Hence a positive real defect would persist
;; at a nearby rational tuple, while every rational tuple is already a real
;; tuple. The rational presentation below is therefore bidirectionally
;; equivalent to the source's arbitrary real family, not a domain restriction.
;;
;; The even Leibniz partial sums increase to pi. Thus the union, over
;; domain-precision, of the rational intervals
;;
;;   (0, putnam-1978-a5-pi-lower(domain-precision))
;;
;; is exactly the rational part of (0,pi). Since domain-precision is
;; universally quantified with the other defun arguments, every rational
;; tuple in the source domain is captured once a sufficiently large lower
;; approximant is used.

(defun putnam-1978-a5-factorial (n)
  (if (zp n)
      1
    (* n
       (putnam-1978-a5-factorial (- n 1)))))

(defun putnam-1978-a5-leibniz-prefix (terms)
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1978-a5-leibniz-prefix index)
         (/ sign (+ (* 2 index) 1))))))

(defun putnam-1978-a5-pi-lower (domain-precision)
  (* 4
     (putnam-1978-a5-leibniz-prefix
      (* 2 (+ 1 (nfix domain-precision))))))

(defun putnam-1978-a5-positive-rational-list-below-p
    (values bound)
  (if (consp values)
      (and
       (rationalp (car values))
       (< 0 (car values))
       (< (car values) bound)
       (putnam-1978-a5-positive-rational-list-below-p
        (cdr values) bound))
    (equal values nil)))

(defun putnam-1978-a5-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-1978-a5-sum (cdr values)))
    0))

(defun putnam-1978-a5-product (values)
  (if (consp values)
      (* (car values)
         (putnam-1978-a5-product (cdr values)))
    1))

;; This is the Maclaurin prefix
;;
;;   sum_(j < terms) (-1)^j x^(2j+1)/(2j+1)!.
(defun putnam-1978-a5-sine-prefix (x terms)
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1978-a5-sine-prefix x index)
         (/ (* sign (expt x degree))
            (putnam-1978-a5-factorial degree))))))

(defun putnam-1978-a5-sinc-prefix-product (values terms)
  (if (consp values)
      (* (/ (putnam-1978-a5-sine-prefix
             (car values) terms)
            (car values))
         (putnam-1978-a5-sinc-prefix-product
          (cdr values) terms))
    1))

(defun putnam-1978-a5-prefix-defect (values n terms)
  (let* ((mean
          (/ (putnam-1978-a5-sum values) n))
         (left-prefix
          (putnam-1978-a5-sinc-prefix-product
           values terms))
         (mean-prefix
          (/ (putnam-1978-a5-sine-prefix mean terms)
             mean)))
    (- left-prefix
       (expt mean-prefix n))))

;; For each fixed rational tuple, the prefix defect converges to the exact
;; source defect. The exact inequality defect <= 0 is therefore equivalent
;; to saying that every positive rational tolerance eventually bounds every
;; sufficiently long prefix defect. The cutoff is existential: no convergence
;; rate beyond the source proposition is asserted.
(defun-sk putnam-1978-a5-tail-p
    (values n epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (< (putnam-1978-a5-prefix-defect
         values n terms)
        epsilon))))

(defun-sk putnam-1978-a5-cutoff-exists-p
    (values n epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (< 0 cutoff)
     (putnam-1978-a5-tail-p
      values n epsilon cutoff))))

(defun putnambench-putnam-1978-a5-statement
    (values n domain-precision epsilon)
  (implies
   (and
    (natp n)
    (< 0 n)
    (natp domain-precision)
    (rationalp epsilon)
    (< 0 epsilon)
    (equal (len values) n)
    (putnam-1978-a5-positive-rational-list-below-p
     values
     (putnam-1978-a5-pi-lower domain-precision)))
   (putnam-1978-a5-cutoff-exists-p
    values n epsilon)))

(value-triple :itpeval-statement-checked)
:q
