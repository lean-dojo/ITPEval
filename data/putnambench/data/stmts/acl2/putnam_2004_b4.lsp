;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_b4:
;; composing the rotations through angle 2*pi/n about (1,0), ..., (n,0)
;; translates every complex point by n. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Put zeta = exp(2*pi*i/n).  Each source rotation is the affine map
;;
;;   Q |-> zeta*Q + (1-zeta)*k.
;;
;; The polynomial pair (A,B) below represents Q |-> A(zeta)*Q+B(zeta).
;; Starting from the identity and composing the rotations for k=1,...,n
;; therefore gives exactly the source map R n.  The claimed translation is
;; Q |-> Q+n, so equality as functions on all complex Q is equivalent to
;; A(zeta)=1 and B(zeta)=n.
;;
;; Since zeta is a primitive n-th root of unity, its minimal polynomial over
;; the rationals is Phi_n.  Each coefficient equality holds exactly when its
;; polynomial difference is divisible by Phi_n.  Thus the two remainder
;; tests preserve the arbitrary complex domain and are bidirectionally
;; equivalent to the source function equality; they do not replace complex
;; values by ACL2's complex rationals.  The source parameters R and Rk are
;; eliminated only by unfolding the hypotheses that uniquely define them.

;; Polynomials use rational coefficient lists in ascending degree order.

(defun putnam-2004-b4-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-2004-b4-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-2004-b4-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-2004-b4-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-2004-b4-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-2004-b4-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-2004-b4-poly-negate (polynomial)
  (putnam-2004-b4-poly-scale -1 polynomial))

(defun putnam-2004-b4-poly-subtract (left right)
  (putnam-2004-b4-poly-normalize
   (putnam-2004-b4-poly-add
    left
    (putnam-2004-b4-poly-negate right))))

(defun putnam-2004-b4-poly-multiply (left right)
  (if (consp left)
      (putnam-2004-b4-poly-normalize
       (putnam-2004-b4-poly-add
        (putnam-2004-b4-poly-scale (car left) right)
        (cons 0
              (putnam-2004-b4-poly-multiply
               (cdr left) right))))
    nil))

(defun putnam-2004-b4-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-2004-b4-zero-list (- count 1)))))

(defun putnam-2004-b4-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-2004-b4-zero-list degree)
     (list coefficient))))

(defun putnam-2004-b4-poly-degree (polynomial)
  (let ((normalized
         (putnam-2004-b4-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-2004-b4-poly-leading-coefficient (polynomial)
  (let ((normalized
         (putnam-2004-b4-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-2004-b4-poly-degree normalized)
             normalized)
      0)))

;; The step bound exceeds the number of degree reductions required by
;; polynomial long division with a nonzero divisor.
(defun putnam-2004-b4-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons (putnam-2004-b4-poly-normalize quotient)
            (putnam-2004-b4-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-2004-b4-poly-normalize remainder))
           (normalized-divisor
            (putnam-2004-b4-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-2004-b4-poly-degree
                  normalized-remainder)
                 (putnam-2004-b4-poly-degree
                  normalized-divisor)))
          (cons (putnam-2004-b4-poly-normalize quotient)
                normalized-remainder)
        (let* ((degree-difference
                (- (putnam-2004-b4-poly-degree
                    normalized-remainder)
                   (putnam-2004-b4-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (putnam-2004-b4-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-2004-b4-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-2004-b4-poly-monomial
                 coefficient degree-difference)))
          (putnam-2004-b4-poly-divmod-steps
           (putnam-2004-b4-poly-subtract
            normalized-remainder
            (putnam-2004-b4-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (putnam-2004-b4-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-2004-b4-poly-divmod (dividend divisor)
  (putnam-2004-b4-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len (putnam-2004-b4-poly-normalize dividend)))))

(defun putnam-2004-b4-poly-quotient (dividend divisor)
  (car (putnam-2004-b4-poly-divmod dividend divisor)))

(defun putnam-2004-b4-poly-remainder (dividend divisor)
  (cdr (putnam-2004-b4-poly-divmod dividend divisor)))

(defun putnam-2004-b4-x-to-n-minus-one (n)
  (putnam-2004-b4-poly-add
   (list -1)
   (putnam-2004-b4-poly-monomial 1 n)))

;; The list PRECEDING contains Phi_1 through Phi_(n-1).
(defun putnam-2004-b4-proper-divisor-product
    (n divisor preceding)
  (declare (xargs :measure (nfix divisor)))
  (if (zp divisor)
      (list 1)
    (let ((remaining
           (putnam-2004-b4-proper-divisor-product
            n (- divisor 1) preceding)))
      (if (equal (mod n divisor) 0)
          (putnam-2004-b4-poly-multiply
           (nth (- divisor 1) preceding)
           remaining)
        remaining))))

;; Phi_n = (X^n - 1) / product_(d | n, d < n) Phi_d.
(defun putnam-2004-b4-cyclotomic-list (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (let* ((preceding
            (putnam-2004-b4-cyclotomic-list (- n 1)))
           (proper-divisor-product
            (putnam-2004-b4-proper-divisor-product
             n (- n 1) preceding))
           (phi-n
            (putnam-2004-b4-poly-quotient
             (putnam-2004-b4-x-to-n-minus-one n)
             proper-divisor-product)))
      (append
       preceding
       (list (putnam-2004-b4-poly-normalize phi-n))))))

(defun putnam-2004-b4-cyclotomic-polynomial (n)
  (if (zp n)
      nil
    (nth (- n 1)
         (putnam-2004-b4-cyclotomic-list n))))

;; AFFINE is (A B), representing Q |-> A(zeta)*Q+B(zeta).
(defun putnam-2004-b4-compose-rotations
    (remaining k affine)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      affine
    (let* ((x-polynomial (list 0 1))
           (one-minus-x (list 1 -1))
           (a (car affine))
           (b (cadr affine))
           (next-a
            (putnam-2004-b4-poly-multiply
             x-polynomial a))
           (next-b
            (putnam-2004-b4-poly-add
             (putnam-2004-b4-poly-multiply
              x-polynomial b)
             (putnam-2004-b4-poly-scale
              k one-minus-x))))
      (putnam-2004-b4-compose-rotations
       (- remaining 1)
       (+ k 1)
       (list next-a next-b)))))

(defun putnam-2004-b4-composition-affine (n)
  (putnam-2004-b4-compose-rotations
   n 1 (list (list 1) nil)))

(defun putnambench-putnam-2004-b4-statement (n)
  (implies
   (and (natp n)
        (<= 2 n))
   (let* ((affine
           (putnam-2004-b4-composition-affine n))
          (a-difference
           (putnam-2004-b4-poly-subtract
            (car affine) (list 1)))
          (b-difference
           (putnam-2004-b4-poly-subtract
            (cadr affine) (list n)))
          (phi-n
           (putnam-2004-b4-cyclotomic-polynomial n)))
     (and
      (equal
       (putnam-2004-b4-poly-remainder
        a-difference phi-n)
       nil)
      (equal
       (putnam-2004-b4-poly-remainder
        b-difference phi-n)
       nil)))))

(value-triple :itpeval-statement-checked)
:q
