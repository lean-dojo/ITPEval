;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_b6:
;; the expected right-endpoint Riemann sum over uniformly ordered points in
;; (0,1) is integration against a degree-n polynomial bounded by 0 and 1.
;; This file contains no proof.

(in-package "ACL2")

;; Polynomials are finite lists of rational coefficients in ascending degree
;; order.  These test functions are not a restriction of the source domain:
;; rational polynomials vanishing at 1 are uniformly dense in the continuous
;; real functions on [0,1] that vanish at 1.  Both the expected-sum functional
;; and integration against the bounded polynomial below are continuous in the
;; uniform norm, so equality on these tests is equivalent in both directions
;; to equality for every source function.

(defun putnam-1989-b6-rational-polynomial-p (coefficients)
  (if (consp coefficients)
      (and (rationalp (car coefficients))
           (putnam-1989-b6-rational-polynomial-p
            (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-1989-b6-polynomial-value (coefficients x)
  (if (consp coefficients)
      (+ (car coefficients)
         (* x
            (putnam-1989-b6-polynomial-value
             (cdr coefficients) x)))
    0))

(defun putnam-1989-b6-last-coefficient (coefficients)
  (if (consp (cdr coefficients))
      (putnam-1989-b6-last-coefficient (cdr coefficients))
    (if (consp coefficients) (car coefficients) 0)))

(defun putnam-1989-b6-degree-n-p (coefficients n)
  (and
   (true-listp coefficients)
   (putnam-1989-b6-rational-polynomial-p coefficients)
   (equal (len coefficients) (+ n 1))
   (not
    (equal
     (putnam-1989-b6-last-coefficient coefficients)
     0))))

(defun putnam-1989-b6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1989-b6-factorial (- n 1)))))

;; Midpoint coordinate number INDEX in a SUBDIVISIONS-grid of [0,1].
(defun putnam-1989-b6-grid-coordinate
    (code index subdivisions)
  (if (posp subdivisions)
      (/ (+ (* 2
               (mod
                (floor code
                       (expt subdivisions index))
                subdivisions))
            1)
         (* 2 subdivisions))
    0))

(defun putnam-1989-b6-ordered-grid-point-p
    (code index remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining)
          (equal remaining 1))
      t
    (and
     (< (putnam-1989-b6-grid-coordinate
         code index subdivisions)
        (putnam-1989-b6-grid-coordinate
         code (+ index 1) subdivisions))
     (putnam-1989-b6-ordered-grid-point-p
      code (+ index 1) (- remaining 1)
      subdivisions))))

;; The source right-endpoint sum, including the final interval to 1.
(defun putnam-1989-b6-right-sum-aux
    (function-coefficients code index remaining
                           subdivisions previous)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (* (- 1 previous)
         (putnam-1989-b6-polynomial-value
          function-coefficients 1))
    (let ((current
           (putnam-1989-b6-grid-coordinate
            code index subdivisions)))
      (+ (* (- current previous)
            (putnam-1989-b6-polynomial-value
             function-coefficients current))
         (putnam-1989-b6-right-sum-aux
          function-coefficients code (+ index 1)
          (- remaining 1) subdivisions current)))))

(defun putnam-1989-b6-simplex-summand
    (function-coefficients code n subdivisions)
  (if (putnam-1989-b6-ordered-grid-point-p
       code 0 n subdivisions)
      (putnam-1989-b6-right-sum-aux
       function-coefficients code 0 n subdivisions 0)
    0))

(defun putnam-1989-b6-simplex-grid-sum
    (function-coefficients remaining n subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1989-b6-simplex-summand
        function-coefficients (- remaining 1)
        n subdivisions)
       (putnam-1989-b6-simplex-grid-sum
        function-coefficients (- remaining 1)
        n subdivisions))))

;; The ordered simplex has volume 1/n!, so multiplying its cube Riemann sum
;; by n! gives expectation under the source uniform distribution.
(defun putnam-1989-b6-expected-sum-approx
    (function-coefficients n subdivisions)
  (if (and (posp n)
           (posp subdivisions))
      (* (/ (putnam-1989-b6-factorial n)
            (expt subdivisions n))
         (putnam-1989-b6-simplex-grid-sum
          function-coefficients
          (expt subdivisions n)
          n subdivisions))
    0))

;; Exact integral of t^degree times the polynomial.
(defun putnam-1989-b6-shifted-integral
    (coefficients degree)
  (if (consp coefficients)
      (+ (/ (car coefficients) (+ degree 1))
         (putnam-1989-b6-shifted-integral
          (cdr coefficients) (+ degree 1)))
    0))

(defun putnam-1989-b6-product-integral-aux
    (function-coefficients witness-coefficients degree)
  (if (consp function-coefficients)
      (+ (* (car function-coefficients)
            (putnam-1989-b6-shifted-integral
             witness-coefficients degree))
         (putnam-1989-b6-product-integral-aux
          (cdr function-coefficients)
          witness-coefficients
          (+ degree 1)))
    0))

(defun putnam-1989-b6-product-integral
    (function-coefficients witness-coefficients)
  (putnam-1989-b6-product-integral-aux
   function-coefficients
   witness-coefficients
   0))

;; The simplex indicator is discontinuous only on finitely many hyperplanes,
;; so these midpoint sums converge to the normalized simplex integral.
(defun-sk putnam-1989-b6-expectation-tail-p
    (n function-coefficients witness-coefficients
       epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (< (abs
         (- (putnam-1989-b6-expected-sum-approx
             function-coefficients n subdivisions)
            (putnam-1989-b6-product-integral
             function-coefficients
             witness-coefficients)))
        epsilon))))

(defun-sk putnam-1989-b6-cutoff-exists-p
    (n function-coefficients witness-coefficients epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1989-b6-expectation-tail-p
      n function-coefficients witness-coefficients
      epsilon cutoff))))

(defun-sk putnam-1989-b6-witness-bounds-p
    (witness-coefficients)
  (forall (t-value)
    (implies
     (and
      (rationalp t-value)
      (<= 0 t-value)
      (<= t-value 1))
     (let ((value
            (putnam-1989-b6-polynomial-value
             witness-coefficients t-value)))
       (and
        (<= 0 value)
        (<= value 1))))))

;; Rational polynomials vanishing at 1 are uniformly dense in the source
;; continuous function space. Both sides are bounded linear functionals in
;; the uniform norm, so equality on this test class is equivalent to equality
;; for every source function.
(defun-sk putnam-1989-b6-witness-equality-p
    (n witness-coefficients)
  (forall (function-coefficients epsilon)
    (implies
     (and
      (putnam-1989-b6-rational-polynomial-p
       function-coefficients)
      (equal
       (putnam-1989-b6-polynomial-value
        function-coefficients 1)
       0)
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1989-b6-cutoff-exists-p
      n function-coefficients witness-coefficients
      epsilon))))

(defun-sk putnambench-putnam-1989-b6-statement (n)
  (exists (witness-coefficients)
    (implies
     (and
      (natp n)
      (< 0 n))
     (and
      (putnam-1989-b6-degree-n-p
       witness-coefficients n)
      (putnam-1989-b6-witness-bounds-p
       witness-coefficients)
      (putnam-1989-b6-witness-equality-p
       n witness-coefficients)))))

(value-triple :itpeval-statement-checked)
:q
