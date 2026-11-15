;; Statement-only formalization of thousand-theorems corpus artifact Q26708,
;; "Binomial theorem": in every commutative semiring, (x + y)^n equals the
;; sum from m = 0 through n of x^m * y^(n-m) multiplied by choose(n,m).
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent an arbitrary carrier and its
;; semiring operations. The SEMIRING argument is a tag for the source type.

(defstub q26708-member-p (semiring value) t)
(defstub q26708-zero (semiring) t)
(defstub q26708-one (semiring) t)
(defstub q26708-add (semiring left right) t)
(defstub q26708-multiply (semiring left right) t)

;; Exact first-order presentation of Lean's possibly trivial CommSemiring.

(defun-sk q26708-commutative-semiring-laws-p (semiring)
  (forall (x y z)
    (and
     (implies
      (q26708-member-p semiring x)
      (let ((zero (q26708-zero semiring))
            (one (q26708-one semiring)))
        (and
         (equal (q26708-add semiring x zero) x)
         (equal (q26708-add semiring zero x) x)
         (equal (q26708-multiply semiring x one) x)
         (equal (q26708-multiply semiring one x) x)
         (equal (q26708-multiply semiring x zero) zero)
         (equal (q26708-multiply semiring zero x) zero))))
     (implies
      (and
       (q26708-member-p semiring x)
       (q26708-member-p semiring y))
      (and
       (q26708-member-p
        semiring
        (q26708-add semiring x y))
       (q26708-member-p
        semiring
        (q26708-multiply semiring x y))
       (equal
        (q26708-add semiring x y)
        (q26708-add semiring y x))
       (equal
        (q26708-multiply semiring x y)
        (q26708-multiply semiring y x))))
     (implies
      (and
       (q26708-member-p semiring x)
       (q26708-member-p semiring y)
       (q26708-member-p semiring z))
      (and
       (equal
        (q26708-add
         semiring
         (q26708-add semiring x y)
         z)
        (q26708-add
         semiring
         x
         (q26708-add semiring y z)))
       (equal
        (q26708-multiply
         semiring
         (q26708-multiply semiring x y)
         z)
        (q26708-multiply
         semiring
         x
         (q26708-multiply semiring y z)))
       (equal
        (q26708-multiply
         semiring
         x
         (q26708-add semiring y z))
        (q26708-add
         semiring
         (q26708-multiply semiring x y)
         (q26708-multiply semiring x z)))
       (equal
        (q26708-multiply
         semiring
         (q26708-add semiring x y)
         z)
        (q26708-add
         semiring
         (q26708-multiply semiring x z)
         (q26708-multiply semiring y z))))))))

(defun q26708-commutative-semiring-p (semiring)
  (and
   (q26708-member-p semiring (q26708-zero semiring))
   (q26708-member-p semiring (q26708-one semiring))
   (q26708-commutative-semiring-laws-p semiring)))

(defun q26708-r-power (semiring base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q26708-one semiring)
    (q26708-multiply
     semiring
     base
     (q26708-r-power semiring base (1- exponent)))))

(defun q26708-r-nat (semiring n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q26708-zero semiring)
    (q26708-add
     semiring
     (q26708-one semiring)
     (q26708-r-nat semiring (1- n)))))

(defun q26708-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (not (natp k))
          (< n k))
      0
    (if (or (zp k)
            (equal n k))
        1
      (+ (q26708-binomial-coefficient (1- n) (1- k))
         (q26708-binomial-coefficient (1- n) k)))))

(defun q26708-binomial-term (semiring x y n m)
  (q26708-multiply
   semiring
   (q26708-multiply
    semiring
    (q26708-r-power semiring x m)
    (q26708-r-power semiring y (- n m)))
   (q26708-r-nat
    semiring
    (q26708-binomial-coefficient n m))))

;; COUNT = n + 1 enumerates m = n,n-1,...,0. Commutativity of addition makes
;; this the same finite sum as Lean's Finset.range (n + 1).

(defun q26708-binomial-sum (semiring x y n count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q26708-zero semiring)
    (let ((m (1- count)))
      (q26708-add
       semiring
       (q26708-binomial-term semiring x y n m)
       (q26708-binomial-sum
        semiring x y n (1- count))))))

(defun thousand-theorems-q26708-binomial-theorem-statement
    (semiring x y n)
  (implies
   (and
    (q26708-commutative-semiring-p semiring)
    (q26708-member-p semiring x)
    (q26708-member-p semiring y)
    (natp n))
   (equal
    (q26708-r-power
     semiring
     (q26708-add semiring x y)
     n)
    (q26708-binomial-sum
     semiring x y n (+ n 1)))))

(value-triple :itpeval-statement-checked)
:q
