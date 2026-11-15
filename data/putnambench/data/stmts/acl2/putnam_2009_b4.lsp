;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_b4:
;; the real dimension of the space of balanced bivariate polynomials of total
;; degree at most 2009 is 2020050. This file contains no proof.
;;
;; Coefficients are ordered by total degree, with x^i*y^j at index
;; ((i+j)(i+j+1))/2+i. Thus the coefficient space has
;; (2010*2011)/2 = 2021055 coordinates.
;;
;; On a circle centered at the origin, monomials with an odd exponent have
;; zero integral. In even total degree 2k, after removing the common nonzero
;; factor, the circle-average equation is
;;
;;   sum_{a=0}^k
;;     ((2a)!/a!)*((2(k-a))!/(k-a)!) c_(2a,2(k-a)) = 0.
;;
;; The functions below are therefore an exact sparse encoding of the rational
;; 1005-by-2021055 constraint matrix. Vanishing of its product with a real
;; coefficient vector is bidirectionally equivalent to balancedness on every
;; circle. Since this matrix has rational entries, scalar extension from Q to
;; R preserves its rank and kernel dimension. Consequently, existence of the
;; finite rational kernel basis stated below is bidirectionally equivalent to
;; the requested real dimension. The basis is internally existentially
;; quantified; it is not an external parameter.

(in-package "ACL2")

(set-inhibit-warnings "Invariant-risk")

(set-irrelevant-formals-ok t)

(defun putnam-2009-b4-zero-vector (length)
  (if (zp length)
      nil
    (cons 0
          (putnam-2009-b4-zero-vector (- length 1)))))

(defun putnam-2009-b4-rational-vector-p (vector length)
  (if (zp length)
      (equal vector nil)
    (and (consp vector)
         (rationalp (car vector))
         (putnam-2009-b4-rational-vector-p
          (cdr vector)
          (- length 1)))))

(defun putnam-2009-b4-rational-matrix-p (matrix rows columns)
  (if (zp rows)
      (equal matrix nil)
    (and (consp matrix)
         (putnam-2009-b4-rational-vector-p (car matrix) columns)
         (putnam-2009-b4-rational-matrix-p
          (cdr matrix)
          (- rows 1)
          columns))))

(defun putnam-2009-b4-vector-add (left right)
  (if (and (consp left)
           (consp right))
      (cons (+ (car left) (car right))
            (putnam-2009-b4-vector-add (cdr left) (cdr right)))
    nil))

(defun putnam-2009-b4-vector-smul (scalar vector)
  (if (consp vector)
      (cons (* scalar (car vector))
            (putnam-2009-b4-vector-smul scalar (cdr vector)))
    nil))

(defun putnam-2009-b4-monomial-index (x-exponent y-exponent)
  (let ((degree (+ x-exponent y-exponent)))
    (+ (floor (* degree (+ degree 1)) 2)
       x-exponent)))

(defun putnam-2009-b4-product-range (start count)
  (if (zp count)
      1
    (* start
       (putnam-2009-b4-product-range
        (+ start 1)
        (- count 1)))))

(defun putnam-2009-b4-half-factorial-ratio (n)
  ; (2n)!/n! = (n+1)(n+2)...(2n).
  (putnam-2009-b4-product-range (+ n 1) n))

(defun putnam-2009-b4-circle-weight (a b)
  (* (putnam-2009-b4-half-factorial-ratio a)
     (putnam-2009-b4-half-factorial-ratio b)))

(defun putnam-2009-b4-constraint-row-sum
  (coefficients degree-index a-count)
  (if (zp a-count)
      0
    (let* ((a (- a-count 1))
           (b (- degree-index a))
           (coefficient-index
            (putnam-2009-b4-monomial-index (* 2 a) (* 2 b))))
      (+ (* (putnam-2009-b4-circle-weight a b)
            (nth coefficient-index coefficients))
         (putnam-2009-b4-constraint-row-sum
          coefficients
          degree-index
          (- a-count 1))))))

(defun putnam-2009-b4-constraint-matrix-times-vector
  (coefficients row-count)
  (if (zp row-count)
      nil
    (let ((degree-index (- row-count 1)))
      (cons
       (putnam-2009-b4-constraint-row-sum
        coefficients
        degree-index
        (+ degree-index 1))
       (putnam-2009-b4-constraint-matrix-times-vector
        coefficients
        (- row-count 1))))))

(defun putnam-2009-b4-balanced-vector-p (coefficients)
  (and
   (putnam-2009-b4-rational-vector-p coefficients 2021055)
   (equal
    (putnam-2009-b4-constraint-matrix-times-vector coefficients 1005)
    (putnam-2009-b4-zero-vector 1005))))

(defun putnam-2009-b4-basis-vectors-in-kernel-p (basis)
  (if (consp basis)
      (and (putnam-2009-b4-balanced-vector-p (car basis))
           (putnam-2009-b4-basis-vectors-in-kernel-p (cdr basis)))
    (equal basis nil)))

(defun putnam-2009-b4-linear-combination
  (basis coefficients ambient-dimension)
  (if (and (consp basis)
           (consp coefficients))
      (putnam-2009-b4-vector-add
       (putnam-2009-b4-vector-smul (car coefficients) (car basis))
       (putnam-2009-b4-linear-combination
        (cdr basis)
        (cdr coefficients)
        ambient-dimension))
    (putnam-2009-b4-zero-vector ambient-dimension)))

(defun-sk putnam-2009-b4-representation-exists-p (basis vector)
  (exists
   (coordinates)
   (and
    (putnam-2009-b4-rational-vector-p coordinates (len basis))
    (equal
     (putnam-2009-b4-linear-combination basis coordinates 2021055)
     vector))))

(defun-sk putnam-2009-b4-basis-spans-kernel-p (basis)
  (forall
   (vector)
   (implies
    (putnam-2009-b4-balanced-vector-p vector)
    (putnam-2009-b4-representation-exists-p basis vector))))

(defun-sk putnam-2009-b4-basis-independent-p (basis)
  (forall
   (coordinates)
   (implies
    (and
     (putnam-2009-b4-rational-vector-p coordinates (len basis))
     (equal
      (putnam-2009-b4-linear-combination basis coordinates 2021055)
      (putnam-2009-b4-zero-vector 2021055)))
    (equal coordinates
           (putnam-2009-b4-zero-vector (len basis))))))

(defun putnam-2009-b4-rational-kernel-basis-p (basis)
  (and
   (putnam-2009-b4-rational-matrix-p basis (len basis) 2021055)
   (putnam-2009-b4-basis-vectors-in-kernel-p basis)
   (putnam-2009-b4-basis-independent-p basis)
   (putnam-2009-b4-basis-spans-kernel-p basis)))

(defun-sk putnam-2009-b4-kernel-dimension-p (dimension)
  (exists
   (basis)
   (and
    (natp dimension)
    (equal (len basis) dimension)
    (putnam-2009-b4-rational-kernel-basis-p basis))))

(defun putnam-2009-b4-solution ()
  2020050)

(defun putnambench-putnam-2009-b4-statement ()
  (putnam-2009-b4-kernel-dimension-p
   (putnam-2009-b4-solution)))

(value-triple :itpeval-statement-checked)
:q
