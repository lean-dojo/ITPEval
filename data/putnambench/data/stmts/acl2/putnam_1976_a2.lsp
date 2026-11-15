;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_a2:
;; for every positive n, one of two specified symmetric integer polynomials
;; is an integer polynomial in P=x*y*(x+y) and Q=x^2+x*y+y^2. This file
;; contains no proof.

(in-package "ACL2")

;; Put s=x+y and e=x*y. A homogeneous symmetric polynomial of degree n is
;; encoded by the integer list (c_0 ... c_floor(n/2)) representing
;;
;;   sum_k c_k * s^(n-2k) * e^k.
;;
;; In these coordinates P=s*e and Q=s^2-e. The power sum x^n+y^n obeys
;; R_0=2, R_1=s, and R_n=s*R_(n-1)-e*R_(n-2), so the coefficient lists below
;; encode exactly F_n=s^n-R_n and G_n=s^n+R_n.
;;
;; The substitution homomorphism Z[U,V] -> Z[s,e] given by U=s*e and
;; V=s^2-e is injective (U and V are algebraically independent). Therefore a
;; polynomial A(U,V) can evaluate to a homogeneous form of degree n exactly
;; when its weighted-degree-n part does. Its possible monomials are U^i V^j
;; with 3*i+2*j=n. In the displayed coefficient encoding,
;;
;;   U^i V^j = s^i e^i (s^2-e)^j
;;
;; has first nonzero coefficient 1 at index i. Increasing the admissible i by
;; two hence gives a unit-triangular integer basis. The reduction below is
;; zero exactly when an internal integer-polynomial witness A exists; no
;; witness is exposed as a statement parameter.

(defun putnam-1976-a2-form-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-1976-a2-form-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1976-a2-form-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1976-a2-form-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1976-a2-form-scale (scalar coefficients)
  (if (consp coefficients)
      (cons (* scalar (car coefficients))
            (putnam-1976-a2-form-scale
             scalar (cdr coefficients)))
    nil))

(defun putnam-1976-a2-form-subtract (left right)
  (putnam-1976-a2-form-normalize
   (putnam-1976-a2-form-add
    left
    (putnam-1976-a2-form-scale -1 right))))

(defun putnam-1976-a2-zero-prefix (count coefficients)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      coefficients
    (cons 0
          (putnam-1976-a2-zero-prefix
           (- count 1) coefficients))))

(defun putnam-1976-a2-form-coefficient (index coefficients)
  (let ((coefficient (nth (nfix index) coefficients)))
    (if (integerp coefficient)
        coefficient
      0)))

;; Multiplication by s leaves the coefficient indices unchanged, while
;; multiplication by e prefixes one zero.
(defun putnam-1976-a2-power-sum-coefficients (n)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) (list 2))
   ((equal n 1) (list 1))
   (t
    (putnam-1976-a2-form-subtract
     (putnam-1976-a2-power-sum-coefficients
      (- n 1))
     (cons
      0
      (putnam-1976-a2-power-sum-coefficients
       (- n 2)))))))

(defun putnam-1976-a2-f-coefficients (n)
  (putnam-1976-a2-form-subtract
   (list 1)
   (putnam-1976-a2-power-sum-coefficients n)))

(defun putnam-1976-a2-g-coefficients (n)
  (putnam-1976-a2-form-normalize
   (putnam-1976-a2-form-add
    (list 1)
    (putnam-1976-a2-power-sum-coefficients n))))

;; Coefficients of Q^j=(s^2-e)^j.
(defun putnam-1976-a2-q-power-coefficients (j)
  (declare (xargs :measure (nfix j)))
  (if (zp j)
      (list 1)
    (let ((previous
           (putnam-1976-a2-q-power-coefficients
            (- j 1))))
      (putnam-1976-a2-form-subtract
       previous
       (cons 0 previous)))))

;; Coefficients of P^i*Q^j.
(defun putnam-1976-a2-basis-coefficients (i j)
  (putnam-1976-a2-zero-prefix
   i
   (putnam-1976-a2-q-power-coefficients j)))

(defun putnam-1976-a2-basis-count (n)
  (let* ((n (nfix n))
         (first-i (mod n 2))
         (maximum-i (floor n 3)))
    (if (< maximum-i first-i)
        0
      (+ 1 (floor (- maximum-i first-i) 2)))))

;; Eliminate the unique coefficient of each admissible P^i*Q^j in increasing
;; order of i. The step count enumerates precisely all nonnegative solutions
;; of 3*i+2*j=n.
(defun putnam-1976-a2-reduce-weighted-form
    (coefficients n i steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (putnam-1976-a2-form-normalize coefficients)
    (let* ((coefficients
            (putnam-1976-a2-form-normalize coefficients))
           (coefficient
            (putnam-1976-a2-form-coefficient
             i coefficients))
           (j
            (floor (- (nfix n) (* 3 (nfix i))) 2))
           (basis
            (putnam-1976-a2-basis-coefficients
             i j)))
      (putnam-1976-a2-reduce-weighted-form
       (putnam-1976-a2-form-subtract
        coefficients
        (putnam-1976-a2-form-scale
         coefficient basis))
       n
       (+ (nfix i) 2)
       (- steps 1)))))

(defun putnam-1976-a2-polynomial-in-p-q-p
    (coefficients n)
  (equal
   (putnam-1976-a2-reduce-weighted-form
    coefficients
    n
    (mod (nfix n) 2)
    (putnam-1976-a2-basis-count n))
   nil))

(defun putnambench-putnam-1976-a2-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (or
    (putnam-1976-a2-polynomial-in-p-q-p
     (putnam-1976-a2-f-coefficients n)
     n)
    (putnam-1976-a2-polynomial-in-p-q-p
     (putnam-1976-a2-g-coefficients n)
     n))))

(value-triple :itpeval-statement-checked)
:q
