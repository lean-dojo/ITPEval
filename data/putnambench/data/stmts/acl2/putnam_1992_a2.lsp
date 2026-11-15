;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_a2:
;; evaluation as 1992 of a real integral involving the 1992nd Taylor
;; coefficient of (1+x)^alpha. This file contains no proof.

(in-package "ACL2")

(defun putnam-1992-a2-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1992-a2-factorial (- n 1)))))

;; For rational y this is the exact real Taylor coefficient
;;
;;   C(-y-1) = product_(k=1)^1992 (y+k) / 1992!.
;;
;; Thus the rational values below are restrictions of the source real
;; function, rather than a rational approximation to its values.
(defun putnam-1992-a2-shifted-product (y remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      1
    (* (+ y remaining)
       (putnam-1992-a2-shifted-product
        y (- remaining 1)))))

(defun putnam-1992-a2-coefficient (y)
  (/ (putnam-1992-a2-shifted-product y 1992)
     (putnam-1992-a2-factorial 1992)))

(defun putnam-1992-a2-reciprocal-sum (y remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (/ 1 (+ y remaining))
       (putnam-1992-a2-reciprocal-sum
        y (- remaining 1)))))

(defun putnam-1992-a2-integrand (y)
  (* (putnam-1992-a2-coefficient y)
     (putnam-1992-a2-reciprocal-sum y 1992)))

;; Exact rational right Riemann sums on [0,1]. Their limit is the source real
;; interval integral because the displayed integrand is a polynomial: the
;; apparent denominators cancel against the shifted product.
(defun putnam-1992-a2-riemann-sum-aux (grid remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1992-a2-integrand (/ remaining grid))
       (putnam-1992-a2-riemann-sum-aux
        grid (- remaining 1)))))

(defun putnam-1992-a2-riemann-sum (grid)
  (if (posp grid)
      (/ (putnam-1992-a2-riemann-sum-aux grid grid)
         grid)
    0))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; Quantifying the cutoff existentially states only convergence to 1992; it
;; does not bake a particular error estimate into the benchmark statement.
(defun-sk putnam-1992-a2-tail-p (epsilon cutoff)
  (forall (grid)
    (implies
     (and (natp grid)
          (<= cutoff grid))
     (< (abs
         (- (putnam-1992-a2-riemann-sum grid)
            1992))
        epsilon))))

(defun-sk putnam-1992-a2-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1992-a2-tail-p epsilon cutoff))))

(defun-sk putnambench-putnam-1992-a2-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-1992-a2-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
