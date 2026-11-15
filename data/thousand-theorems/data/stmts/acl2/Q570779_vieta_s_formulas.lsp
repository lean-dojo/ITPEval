;; Statement-only formalization of thousand-theorems corpus artifact Q570779,
;; "Vieta's formulas": over an arbitrary commutative semiring, the product of
;; the linear polynomials X + C(r) for a finite multiset of elements r equals
;; the sum whose coefficients are its elementary symmetric functions. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent an arbitrary carrier and its zero,
;; one, addition, and multiplication. A semiring tag selects a structure
;; without enumerating or otherwise restricting its carrier.

(defstub q570779-element-p (semiring value) t)
(defstub q570779-zero (semiring) t)
(defstub q570779-one (semiring) t)
(defstub q570779-add (semiring left right) t)
(defstub q570779-multiply (semiring left right) t)

(defun-sk q570779-commutative-semiring-laws-p (semiring)
  (forall (x y z)
    (and
     (implies
      (and
       (q570779-element-p semiring x)
       (q570779-element-p semiring y))
      (and
       (q570779-element-p
        semiring (q570779-add semiring x y))
       (q570779-element-p
        semiring (q570779-multiply semiring x y))
       (equal
        (q570779-add semiring x y)
        (q570779-add semiring y x))
       (equal
        (q570779-multiply semiring x y)
        (q570779-multiply semiring y x))))
     (implies
      (q570779-element-p semiring x)
      (and
       (equal
        (q570779-add semiring x (q570779-zero semiring))
        x)
       (equal
        (q570779-add semiring (q570779-zero semiring) x)
        x)
       (equal
        (q570779-multiply semiring x (q570779-one semiring))
        x)
       (equal
        (q570779-multiply semiring (q570779-one semiring) x)
        x)
       (equal
        (q570779-multiply semiring x (q570779-zero semiring))
        (q570779-zero semiring))
       (equal
        (q570779-multiply semiring (q570779-zero semiring) x)
        (q570779-zero semiring))))
     (implies
      (and
       (q570779-element-p semiring x)
       (q570779-element-p semiring y)
       (q570779-element-p semiring z))
      (and
       (equal
        (q570779-add
         semiring (q570779-add semiring x y) z)
        (q570779-add
         semiring x (q570779-add semiring y z)))
       (equal
        (q570779-multiply
         semiring (q570779-multiply semiring x y) z)
        (q570779-multiply
         semiring x (q570779-multiply semiring y z)))
       (equal
        (q570779-multiply
         semiring x (q570779-add semiring y z))
        (q570779-add
         semiring
         (q570779-multiply semiring x y)
         (q570779-multiply semiring x z)))
       (equal
        (q570779-multiply
         semiring (q570779-add semiring x y) z)
        (q570779-add
         semiring
         (q570779-multiply semiring x z)
         (q570779-multiply semiring y z))))))))

(defun q570779-commutative-semiring-p (semiring)
  (and
   (q570779-element-p semiring (q570779-zero semiring))
   (q570779-element-p semiring (q570779-one semiring))
   (q570779-commutative-semiring-laws-p semiring)))

;; A proper list represents a finite multiset, preserving repetitions. The
;; order is immaterial to the universally quantified identity.

(defun q570779-multiset-p (semiring elements)
  (if (consp elements)
      (and
       (q570779-element-p semiring (car elements))
       (q570779-multiset-p semiring (cdr elements)))
    (equal elements nil)))

;; Coefficient lists are in ascending degree order. Multiplication by X + C(r)
;; sends (a_0,...,a_d) to
;; (a_0*r, a_1*r+a_0, ..., a_d*r+a_(d-1), a_d).

(defun q570779-multiply-by-linear-aux
    (semiring coefficients root previous)
  (declare (xargs :measure (acl2-count coefficients)))
  (if (consp coefficients)
      (cons
       (q570779-add
        semiring
        (q570779-multiply semiring (car coefficients) root)
        previous)
       (q570779-multiply-by-linear-aux
        semiring
        (cdr coefficients)
        root
        (car coefficients)))
    (list previous)))

(defun q570779-multiply-by-linear
    (semiring coefficients root)
  (q570779-multiply-by-linear-aux
   semiring coefficients root (q570779-zero semiring)))

(defun q570779-product-linear-coefficients
    (semiring elements)
  (declare (xargs :measure (acl2-count elements)))
  (if (consp elements)
      (q570779-multiply-by-linear
       semiring
       (q570779-product-linear-coefficients
        semiring (cdr elements))
       (car elements))
    (list (q570779-one semiring))))

;; The elementary symmetric function e_j, including e_0 = 1.

(defun q570779-elementary-symmetric
    (semiring elements degree)
  (declare (xargs :measure (acl2-count elements)))
  (if (zp degree)
      (q570779-one semiring)
    (if (consp elements)
        (q570779-add
         semiring
         (q570779-elementary-symmetric
          semiring (cdr elements) degree)
         (q570779-multiply
          semiring
          (car elements)
          (q570779-elementary-symmetric
           semiring (cdr elements) (- degree 1))))
      (q570779-zero semiring))))

;; The coefficient list of
;; sum_{j=0}^n C(e_j) * X^(n-j) is (e_n,e_(n-1),...,e_0).

(defun q570779-vieta-sum-coefficients-aux
    (semiring elements degree)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      (list
       (q570779-elementary-symmetric
        semiring elements 0))
    (cons
     (q570779-elementary-symmetric
      semiring elements degree)
     (q570779-vieta-sum-coefficients-aux
      semiring elements (- degree 1)))))

(defun q570779-vieta-sum-coefficients
    (semiring elements)
  (q570779-vieta-sum-coefficients-aux
   semiring elements (len elements)))

(defun-sk thousand-theorems-q570779-vieta-s-formulas-statement ()
  (forall (semiring elements)
    (implies
     (and
      (q570779-commutative-semiring-p semiring)
      (q570779-multiset-p semiring elements))
     (equal
      (q570779-product-linear-coefficients
       semiring elements)
      (q570779-vieta-sum-coefficients
       semiring elements)))))

(value-triple :itpeval-statement-checked)
:q
