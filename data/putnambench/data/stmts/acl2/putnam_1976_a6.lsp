;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_a6:
;; every twice continuously differentiable real function bounded in absolute
;; value by 1, with f(0)^2 + f'(0)^2 = 4, has a real zero of f + f''.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source theorem is encoded by the absence of its counterexamples.  A
;; code below denotes a rational piecewise-polynomial C2 function on a finite
;; interval, extended by constants on both tails.  Positive rational widths
;; give the segment domains, and each coefficient list is the ascending
;; monomial expansion in the local coordinate u in [0,1].
;;
;; This is a bidirectionally counterexample-preserving representation.
;;
;; * Every valid code is an actual global C2 real function.  Matching values
;;   and first two derivatives give C2 joins, including the constant tails.
;;   Bernstein coefficients in [-1,1] certify |f| <= 1 on every segment.
;;   Strictly positive Bernstein coefficients for either f + f'' or its
;;   negative certify that this continuous function has no real zero.
;;
;; * Conversely, suppose a source counterexample exists.  Its continuous
;;   nonzero f + f'' has one sign; negate f if necessary.  For
;;   E = f^2 + (f')^2, E' = 2*f'*(f + f'').  Since f'(0) is nonzero, a small
;;   translation in the direction in which E increases gives E > 4.  Scaling
;;   the translated function back to E = 4 makes the bound |f| < 1 strict
;;   while preserving the sign of f + f''.  The function can then be joined,
;;   outside a compact interval, through C2 transitions to small positive
;;   constants while retaining both strict inequalities.  C2 approximation
;;   with interpolation at zero, density of rational points on
;;   a^2 + b^2 = 4, and rational polynomial splines produce a code below.
;;   Sufficient Bernstein degree elevation supplies all finite certificates.
;;
;; Thus the finite data are exact counterexample certificates for the
;; arbitrary-function theorem, rather than samples or a finite function table.

(defun putnam-1976-a6-rational-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (putnam-1976-a6-rational-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1976-a6-polynomial-value (coefficients point)
  (if (consp coefficients)
      (+ (car coefficients)
         (* point
            (putnam-1976-a6-polynomial-value
             (cdr coefficients) point)))
    0))

(defun putnam-1976-a6-derivative-aux
    (coefficients multiplier)
  (if (consp coefficients)
      (cons (* multiplier (car coefficients))
            (putnam-1976-a6-derivative-aux
             (cdr coefficients) (+ multiplier 1)))
    nil))

(defun putnam-1976-a6-derivative (coefficients)
  (if (consp coefficients)
      (putnam-1976-a6-derivative-aux
       (cdr coefficients) 1)
    nil))

(defun putnam-1976-a6-scale-polynomial
    (factor coefficients)
  (if (consp coefficients)
      (cons (* factor (car coefficients))
            (putnam-1976-a6-scale-polynomial
             factor (cdr coefficients)))
    nil))

(defun putnam-1976-a6-add-polynomials (left right)
  (declare (xargs :measure (+ (acl2-count left)
                              (acl2-count right))))
  (cond
   ((consp left)
    (cons (+ (car left)
             (if (consp right) (car right) 0))
          (putnam-1976-a6-add-polynomials
           (cdr left)
           (if (consp right) (cdr right) nil))))
   ((consp right)
    (cons (car right)
          (putnam-1976-a6-add-polynomials
           nil (cdr right))))
   (t nil)))

(defun putnam-1976-a6-forcing-coefficients
    (coefficients width sign)
  (let* ((first-derivative
          (putnam-1976-a6-derivative coefficients))
         (second-derivative
          (putnam-1976-a6-derivative first-derivative))
         (scaled-second-derivative
          (putnam-1976-a6-scale-polynomial
           (/ 1 (* width width))
           second-derivative)))
    (putnam-1976-a6-scale-polynomial
     sign
     (putnam-1976-a6-add-polynomials
      coefficients scaled-second-derivative))))

(defun putnam-1976-a6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1976-a6-factorial (- n 1)))))

(defun putnam-1976-a6-binomial (n k)
  (if (and (natp n)
           (natp k)
           (<= k n))
      (/ (putnam-1976-a6-factorial n)
         (* (putnam-1976-a6-factorial k)
            (putnam-1976-a6-factorial (- n k))))
    0))

(defun putnam-1976-a6-degree-bound (coefficients)
  (if (consp coefficients)
      (- (len coefficients) 1)
    0))

;; For p(u)=sum_i c_i*u^i, the degree-N Bernstein coefficient at k is
;; sum_i c_i*binomial(k,i)/binomial(N,i).
(defun putnam-1976-a6-bernstein-coefficient
    (coefficients total-degree basis-index power)
  (if (consp coefficients)
      (+ (* (car coefficients)
            (/ (putnam-1976-a6-binomial basis-index power)
               (putnam-1976-a6-binomial total-degree power)))
         (putnam-1976-a6-bernstein-coefficient
          (cdr coefficients)
          total-degree
          basis-index
          (+ power 1)))
    0))

(defun putnam-1976-a6-naturals-down-from (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list 0)
    (cons n
          (putnam-1976-a6-naturals-down-from (- n 1)))))

(defun putnam-1976-a6-bernstein-unit-bounds-p
    (coefficients total-degree basis-indices)
  (if (consp basis-indices)
      (let ((coefficient
             (putnam-1976-a6-bernstein-coefficient
              coefficients
              total-degree
              (car basis-indices)
              0)))
        (and
         (<= -1 coefficient)
         (<= coefficient 1)
         (putnam-1976-a6-bernstein-unit-bounds-p
          coefficients
          total-degree
          (cdr basis-indices))))
    (equal basis-indices nil)))

(defun putnam-1976-a6-unit-bound-certificate-p
    (coefficients certificate-degree)
  (and
   (natp certificate-degree)
   (<= (putnam-1976-a6-degree-bound coefficients)
       certificate-degree)
   (putnam-1976-a6-bernstein-unit-bounds-p
    coefficients
    certificate-degree
    (putnam-1976-a6-naturals-down-from certificate-degree))))

(defun putnam-1976-a6-bernstein-strict-positive-p
    (coefficients total-degree basis-indices)
  (if (consp basis-indices)
      (and
       (< 0
          (putnam-1976-a6-bernstein-coefficient
           coefficients
           total-degree
           (car basis-indices)
           0))
       (putnam-1976-a6-bernstein-strict-positive-p
        coefficients
        total-degree
        (cdr basis-indices)))
    (equal basis-indices nil)))

(defun putnam-1976-a6-positive-certificate-p
    (coefficients certificate-degree)
  (and
   (natp certificate-degree)
   (<= (putnam-1976-a6-degree-bound coefficients)
       certificate-degree)
   (putnam-1976-a6-bernstein-strict-positive-p
    coefficients
    certificate-degree
    (putnam-1976-a6-naturals-down-from certificate-degree))))

(defun putnam-1976-a6-segments-certified-p
    (widths pieces bound-degrees forcing-degrees sign)
  (if (consp widths)
      (and
       (consp pieces)
       (consp bound-degrees)
       (consp forcing-degrees)
       (rationalp (car widths))
       (< 0 (car widths))
       (consp (car pieces))
       (putnam-1976-a6-rational-list-p (car pieces))
       (putnam-1976-a6-unit-bound-certificate-p
        (car pieces) (car bound-degrees))
       (putnam-1976-a6-positive-certificate-p
        (putnam-1976-a6-forcing-coefficients
         (car pieces) (car widths) sign)
        (car forcing-degrees))
       (putnam-1976-a6-segments-certified-p
        (cdr widths)
        (cdr pieces)
        (cdr bound-degrees)
        (cdr forcing-degrees)
        sign))
    (and
     (equal widths nil)
     (equal pieces nil)
     (equal bound-degrees nil)
     (equal forcing-degrees nil))))

(defun putnam-1976-a6-first-derivative-value
    (coefficients point)
  (putnam-1976-a6-polynomial-value
   (putnam-1976-a6-derivative coefficients)
   point))

(defun putnam-1976-a6-second-derivative-value
    (coefficients point)
  (putnam-1976-a6-polynomial-value
   (putnam-1976-a6-derivative
    (putnam-1976-a6-derivative coefficients))
   point))

(defun putnam-1976-a6-c2-joins-p (widths pieces)
  (if (and (consp widths)
           (consp (cdr widths))
           (consp pieces)
           (consp (cdr pieces)))
      (and
       (equal
        (putnam-1976-a6-polynomial-value (car pieces) 1)
        (putnam-1976-a6-polynomial-value (cadr pieces) 0))
       (equal
        (/ (putnam-1976-a6-first-derivative-value
            (car pieces) 1)
           (car widths))
        (/ (putnam-1976-a6-first-derivative-value
            (cadr pieces) 0)
           (cadr widths)))
       (equal
        (/ (putnam-1976-a6-second-derivative-value
            (car pieces) 1)
           (* (car widths) (car widths)))
        (/ (putnam-1976-a6-second-derivative-value
            (cadr pieces) 0)
           (* (cadr widths) (cadr widths))))
       (putnam-1976-a6-c2-joins-p
        (cdr widths) (cdr pieces)))
    t))

(defun putnam-1976-a6-left-tail-compatible-p
    (pieces sign)
  (and
   (consp pieces)
   (equal
    (putnam-1976-a6-first-derivative-value
     (car pieces) 0)
    0)
   (equal
    (putnam-1976-a6-second-derivative-value
     (car pieces) 0)
    0)
   (< 0
      (* sign
         (putnam-1976-a6-polynomial-value
          (car pieces) 0)))))

(defun putnam-1976-a6-right-tail-compatible-p
    (pieces sign)
  (if (consp (cdr pieces))
      (putnam-1976-a6-right-tail-compatible-p
       (cdr pieces) sign)
    (and
     (consp pieces)
     (equal
      (putnam-1976-a6-first-derivative-value
       (car pieces) 1)
      0)
     (equal
      (putnam-1976-a6-second-derivative-value
       (car pieces) 1)
      0)
     (< 0
        (* sign
           (putnam-1976-a6-polynomial-value
            (car pieces) 1))))))

(defun putnam-1976-a6-width-sum (widths)
  (if (consp widths)
      (+ (car widths)
         (putnam-1976-a6-width-sum (cdr widths)))
    0))

(defun putnam-1976-a6-value-at-zero
    (left widths pieces)
  (declare (xargs :measure (acl2-count widths)))
  (if (and (consp widths) (consp pieces))
      (let ((right (+ left (car widths))))
        (if (<= 0 right)
            (putnam-1976-a6-polynomial-value
             (car pieces)
             (/ (- left) (car widths)))
          (putnam-1976-a6-value-at-zero
           right (cdr widths) (cdr pieces))))
    0))

(defun putnam-1976-a6-derivative-at-zero
    (left widths pieces)
  (declare (xargs :measure (acl2-count widths)))
  (if (and (consp widths) (consp pieces))
      (let ((right (+ left (car widths))))
        (if (<= 0 right)
            (/ (putnam-1976-a6-first-derivative-value
                (car pieces)
                (/ (- left) (car widths)))
               (car widths))
          (putnam-1976-a6-derivative-at-zero
           right (cdr widths) (cdr pieces))))
    0))

(defun putnam-1976-a6-spline-counterexample-p
    (left widths pieces bound-degrees forcing-degrees sign)
  (and
   (or (equal sign 1)
       (equal sign -1))
   (rationalp left)
   (<= left 0)
   (consp widths)
   (putnam-1976-a6-segments-certified-p
    widths pieces bound-degrees forcing-degrees sign)
   (<= 0 (+ left (putnam-1976-a6-width-sum widths)))
   (putnam-1976-a6-c2-joins-p widths pieces)
   (putnam-1976-a6-left-tail-compatible-p pieces sign)
   (putnam-1976-a6-right-tail-compatible-p pieces sign)
   (let ((value
          (putnam-1976-a6-value-at-zero
           left widths pieces))
         (derivative
          (putnam-1976-a6-derivative-at-zero
           left widths pieces)))
     (equal (+ (* value value)
               (* derivative derivative))
            4))))

(defun putnambench-putnam-1976-a6-statement
    (left widths pieces bound-degrees forcing-degrees sign)
  (not
   (putnam-1976-a6-spline-counterexample-p
    left widths pieces bound-degrees forcing-degrees sign)))

(value-triple :itpeval-statement-checked)
:q
