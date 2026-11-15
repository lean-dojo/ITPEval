;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_a2:
;; the rational-function sequence starting with 1 and x and satisfying
;; Q_(n+2) = (Q_(n+1)^2 - 1) / Q_n has integer-polynomial terms at every
;; positive index. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Polynomials are finite coefficient lists in ascending degree order.
;; Trailing zeroes are allowed, and polynomial equality ignores them.
;; A rational function is a numerator/denominator pair with nonzero
;; denominator; equality is the usual cross-multiplication relation. This is
;; a presentation of Q(x), not a restriction to polynomial rational
;; functions or to finitely many evaluation points.
;;
;; The base values and recurrence uniquely determine Q in the field Q(x).
;; PUTNAM-2017-A2-SEQUENCE-VALUE therefore definitionally eliminates the
;; source function parameter while retaining the original nonlinear
;; recurrence. Exact polynomial division decides whether its value is the
;; image of an integer polynomial; by uniqueness of quotient and remainder,
;; this is equivalent to the source's internal existential polynomial.

(defun putnam-2017-a2-rational-list-p (coefficients)
  (if (consp coefficients)
      (and
       (rationalp (car coefficients))
       (putnam-2017-a2-rational-list-p (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2017-a2-integer-list-p (coefficients)
  (if (consp coefficients)
      (and
       (integerp (car coefficients))
       (putnam-2017-a2-integer-list-p (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2017-a2-poly-zero-p (polynomial)
  (if (consp polynomial)
      (and
       (equal (car polynomial) 0)
       (putnam-2017-a2-poly-zero-p (cdr polynomial)))
    t))

(defun putnam-2017-a2-poly-equal-p (left right)
  (declare
   (xargs :measure
          (+ (acl2-count left) (acl2-count right))))
  (cond
   ((consp left)
    (and
     (equal (car left)
            (if (consp right) (car right) 0))
     (putnam-2017-a2-poly-equal-p
      (cdr left)
      (if (consp right) (cdr right) nil))))
   ((consp right)
    (and
     (equal (car right) 0)
     (putnam-2017-a2-poly-equal-p nil (cdr right))))
   (t t)))

(defun putnam-2017-a2-poly-add (left right)
  (declare
   (xargs :measure
          (+ (acl2-count left) (acl2-count right))))
  (if (or (consp left) (consp right))
      (cons
       (+ (if (consp left) (car left) 0)
          (if (consp right) (car right) 0))
       (putnam-2017-a2-poly-add
        (if (consp left) (cdr left) nil)
        (if (consp right) (cdr right) nil)))
    nil))

(defun putnam-2017-a2-poly-neg (polynomial)
  (if (consp polynomial)
      (cons
       (- (car polynomial))
       (putnam-2017-a2-poly-neg (cdr polynomial)))
    nil))

(defun putnam-2017-a2-poly-sub (left right)
  (putnam-2017-a2-poly-add
   left
   (putnam-2017-a2-poly-neg right)))

(defun putnam-2017-a2-poly-scale (coefficient polynomial)
  (if (consp polynomial)
      (cons
       (* coefficient (car polynomial))
       (putnam-2017-a2-poly-scale coefficient (cdr polynomial)))
    nil))

(defun putnam-2017-a2-poly-mul (left right)
  (if (consp left)
      (putnam-2017-a2-poly-add
       (putnam-2017-a2-poly-scale (car left) right)
       (cons
        0
        (putnam-2017-a2-poly-mul (cdr left) right)))
    nil))

(defun putnam-2017-a2-ratfunc-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (putnam-2017-a2-rational-list-p (car value))
   (putnam-2017-a2-rational-list-p (cadr value))
   (not (putnam-2017-a2-poly-zero-p (cadr value)))))

(defun putnam-2017-a2-ratfunc-zero ()
  (list nil (list 1)))

(defun putnam-2017-a2-ratfunc-one ()
  (list (list 1) (list 1)))

(defun putnam-2017-a2-ratfunc-x ()
  (list (list 0 1) (list 1)))

(defun putnam-2017-a2-ratfunc-zero-p (value)
  (putnam-2017-a2-poly-zero-p (car value)))

(defun putnam-2017-a2-ratfunc-equal-p (left right)
  (putnam-2017-a2-poly-equal-p
   (putnam-2017-a2-poly-mul (car left) (cadr right))
   (putnam-2017-a2-poly-mul (car right) (cadr left))))

(defun putnam-2017-a2-ratfunc-add (left right)
  (list
   (putnam-2017-a2-poly-add
    (putnam-2017-a2-poly-mul (car left) (cadr right))
    (putnam-2017-a2-poly-mul (car right) (cadr left)))
   (putnam-2017-a2-poly-mul (cadr left) (cadr right))))

(defun putnam-2017-a2-ratfunc-neg (value)
  (list
   (putnam-2017-a2-poly-neg (car value))
   (cadr value)))

(defun putnam-2017-a2-ratfunc-sub (left right)
  (putnam-2017-a2-ratfunc-add
   left
   (putnam-2017-a2-ratfunc-neg right)))

(defun putnam-2017-a2-ratfunc-mul (left right)
  (list
   (putnam-2017-a2-poly-mul (car left) (car right))
   (putnam-2017-a2-poly-mul (cadr left) (cadr right))))

;; Inversion sends zero to zero, as in the field structure used by the Lean
;; source. Otherwise it swaps numerator and denominator.
(defun putnam-2017-a2-ratfunc-inv (value)
  (if (putnam-2017-a2-ratfunc-zero-p value)
      (putnam-2017-a2-ratfunc-zero)
    (list (cadr value) (car value))))

(defun putnam-2017-a2-ratfunc-div (left right)
  (putnam-2017-a2-ratfunc-mul
   left
   (putnam-2017-a2-ratfunc-inv right)))

(defun putnam-2017-a2-poly-normalize (polynomial)
  (if (consp polynomial)
      (let ((tail
             (putnam-2017-a2-poly-normalize (cdr polynomial))))
        (if (and (endp tail)
                 (equal (car polynomial) 0))
            nil
          (cons (car polynomial) tail)))
    nil))

(defun putnam-2017-a2-monomial (coefficient degree)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      (list coefficient)
    (cons
     0
     (putnam-2017-a2-monomial coefficient (- degree 1)))))

;; The fuel is the initial numerator length. Each long-division step cancels
;; its leading term, so this bound is sufficient for the exact quotient and
;; remainder while giving ACL2 an immediate structural termination measure.
(defun putnam-2017-a2-poly-divmod-aux
    (numerator denominator fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((num (putnam-2017-a2-poly-normalize numerator))
        (den (putnam-2017-a2-poly-normalize denominator)))
    (if (or
         (zp fuel)
         (endp num)
         (< (len num) (len den)))
        (list nil num)
      (let* ((degree-difference
              (- (len num) (len den)))
             (coefficient
              (/ (car (last num)) (car (last den))))
             (term
              (putnam-2017-a2-monomial
               coefficient degree-difference))
             (reduced
              (putnam-2017-a2-poly-normalize
               (putnam-2017-a2-poly-sub
                num
                (putnam-2017-a2-poly-mul term den))))
             (recursive-result
              (putnam-2017-a2-poly-divmod-aux
               reduced den (- fuel 1))))
        (list
         (putnam-2017-a2-poly-add
          term (car recursive-result))
         (cadr recursive-result))))))

(defun putnam-2017-a2-poly-divmod (numerator denominator)
  (let ((num (putnam-2017-a2-poly-normalize numerator))
        (den (putnam-2017-a2-poly-normalize denominator)))
    (if (endp den)
        (list nil num)
      (putnam-2017-a2-poly-divmod-aux
       num den (len num)))))

(defun putnam-2017-a2-ratfunc-integer-polynomial-p (value)
  (if (putnam-2017-a2-ratfunc-p value)
      (let ((division
             (putnam-2017-a2-poly-divmod
              (car value) (cadr value))))
        (and
         (putnam-2017-a2-poly-zero-p (cadr division))
         (putnam-2017-a2-integer-list-p
          (putnam-2017-a2-poly-normalize
           (car division)))))
    nil))

(defun putnam-2017-a2-sequence-value (n)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n)
    (putnam-2017-a2-ratfunc-one))
   ((equal n 1)
    (putnam-2017-a2-ratfunc-x))
   (t
    (let ((previous
           (putnam-2017-a2-sequence-value (- n 1)))
          (previous-previous
           (putnam-2017-a2-sequence-value (- n 2))))
      (putnam-2017-a2-ratfunc-div
       (putnam-2017-a2-ratfunc-sub
        (putnam-2017-a2-ratfunc-mul previous previous)
        (putnam-2017-a2-ratfunc-one))
       previous-previous)))))

;; ACL2 universally closes N. The exact division predicate is true exactly
;; when there exists an integer-coefficient polynomial equal to Q_n.
(defun putnambench-putnam-2017-a2-statement (n)
  (implies
   (and
    (natp n)
    (< 0 n))
   (putnam-2017-a2-ratfunc-integer-polynomial-p
    (putnam-2017-a2-sequence-value n))))

(value-triple :itpeval-statement-checked)
:q
