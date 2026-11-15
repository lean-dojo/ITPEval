;; Statement-only formalization of Hundred Theorems artifact 089,
;; "The Factor and Remainder Theorems." Over an arbitrary nontrivial
;; commutative ring, division by X - a has remainder p(a), and X - a divides
;; p exactly when p(a) is zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The defstubs name one arbitrary ring. All ring laws are hypotheses of the
;; final statement, so no particular implementation or extra mathematics is
;; assumed.
(defstub ht089-carrier (x) t)
(defstub ht089-add-op (x y) t)
(defstub ht089-multiply-op (x y) t)
(defstub ht089-negate-op (x) t)

(defun ht089-member-p (x)
  (if (ht089-carrier x) t nil))

(defun ht089-add (x y)
  (ht089-add-op x y))

(defun ht089-multiply (x y)
  (ht089-multiply-op x y))

(defun ht089-negate (x)
  (ht089-negate-op x))

(defun-sk ht089-commutative-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht089-member-p x)
      (ht089-member-p y)
      (ht089-member-p z))
     (and
      (ht089-member-p (ht089-add x y))
      (ht089-member-p (ht089-multiply x y))
      (ht089-member-p (ht089-negate x))
      (equal (ht089-add (ht089-add x y) z)
             (ht089-add x (ht089-add y z)))
      (equal (ht089-add x y)
             (ht089-add y x))
      (equal (ht089-add x zero) x)
      (equal (ht089-add x (ht089-negate x)) zero)
      (equal (ht089-multiply (ht089-multiply x y) z)
             (ht089-multiply x (ht089-multiply y z)))
      (equal (ht089-multiply x y)
             (ht089-multiply y x))
      (equal (ht089-multiply x one) x)
      (equal
       (ht089-multiply x (ht089-add y z))
       (ht089-add
        (ht089-multiply x y)
        (ht089-multiply x z)))))))

(defun ht089-ring-context-p (zero one)
  (and
   (ht089-member-p zero)
   (ht089-member-p one)
   (not (equal zero one))
   (ht089-commutative-ring-laws-p zero one)))

;; Polynomials are finite coefficient lists in ascending powers of X.
(defun ht089-polynomial-p (polynomial)
  (if (consp polynomial)
      (and
       (ht089-member-p (car polynomial))
       (ht089-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun ht089-polynomial-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons
         (ht089-add (car left) (car right))
         (ht089-polynomial-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun ht089-polynomial-scale (scalar polynomial)
  (if (consp polynomial)
      (cons
       (ht089-multiply scalar (car polynomial))
       (ht089-polynomial-scale scalar (cdr polynomial)))
    nil))

(defun ht089-polynomial-shift (zero polynomial)
  (if (consp polynomial)
      (cons zero polynomial)
    nil))

(defun ht089-polynomial-multiply (left right zero)
  (if (consp left)
      (ht089-polynomial-add
       (ht089-polynomial-scale (car left) right)
       (ht089-polynomial-shift
        zero
        (ht089-polynomial-multiply (cdr left) right zero)))
    nil))

(defun ht089-polynomial-evaluate (polynomial point zero)
  (if (consp polynomial)
      (ht089-add
       (car polynomial)
       (ht089-multiply
        point
        (ht089-polynomial-evaluate (cdr polynomial) point zero)))
    zero))

;; Coefficient-list equality modulo trailing zero coefficients.
(defun ht089-polynomial-equal-p (left right zero)
  (declare
   (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((consp left)
    (if (consp right)
        (and
         (equal (car left) (car right))
         (ht089-polynomial-equal-p (cdr left) (cdr right) zero))
      (and
       (equal (car left) zero)
       (ht089-polynomial-equal-p (cdr left) nil zero))))
   ((consp right)
    (and
     (equal (car right) zero)
     (ht089-polynomial-equal-p nil (cdr right) zero)))
   (t t)))

(defun ht089-linear-factor (point one)
  (list (ht089-negate point) one))

(defun ht089-constant-polynomial (value)
  (list value))

;; For p = c0 + c1 X + ... + cn X^n, this returns the coefficients
;; q_i = c_{i+1} + a*c_{i+2} + ... + a^(n-i-1)*cn.
(defun ht089-synthetic-quotient (polynomial point zero)
  (if (and (consp polynomial)
           (consp (cdr polynomial)))
      (cons
       (ht089-polynomial-evaluate (cdr polynomial) point zero)
       (ht089-synthetic-quotient (cdr polynomial) point zero))
    nil))

(defun ht089-remainder-identity-p
    (polynomial point zero one)
  (let* ((quotient
          (ht089-synthetic-quotient polynomial point zero))
         (factor
          (ht089-linear-factor point one))
         (remainder
          (ht089-polynomial-evaluate polynomial point zero))
         (reconstructed
          (ht089-polynomial-add
           (ht089-polynomial-multiply factor quotient zero)
           (ht089-constant-polynomial remainder))))
    (ht089-polynomial-equal-p
     polynomial reconstructed zero)))

;; Divisibility quantifies over an arbitrary quotient, rather than requiring
;; the one quotient selected by the synthetic-division implementation.
(defun-sk ht089-has-linear-factor-p
    (polynomial point zero one)
  (exists (quotient)
    (and
     (true-listp quotient)
     (ht089-polynomial-p quotient)
     (ht089-polynomial-equal-p
      polynomial
      (ht089-polynomial-multiply
       (ht089-linear-factor point one)
       quotient
       zero)
      zero))))

(defun-sk hundred-theorems-089-factor-and-remainder-statement
    (zero one)
  (forall (polynomial point)
    (implies
     (and
      (ht089-ring-context-p zero one)
      (true-listp polynomial)
      (ht089-polynomial-p polynomial)
      (ht089-member-p point))
     (and
      (ht089-remainder-identity-p
       polynomial point zero one)
      (iff
       (equal
        (ht089-polynomial-evaluate polynomial point zero)
        zero)
       (ht089-has-linear-factor-p
        polynomial point zero one))))))

(value-triple :itpeval-statement-checked)
:q
