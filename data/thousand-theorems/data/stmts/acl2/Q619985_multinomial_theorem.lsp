;; Statement-only formalization of thousand-theorems corpus artifact Q619985,
;; "Multinomial theorem": for a finite family of pairwise commuting elements
;; in an arbitrary semiring, the nth power of their sum equals the multinomial
;; sum over all natural exponent assignments of total n. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent the arbitrary source index type,
;; semiring, and function. Tags distinguish instances without enumerating or
;; otherwise restricting their carriers.

(defstub q619985-index-member-p (index-type value) t)
(defstub q619985-scalar-member-p (semiring value) t)
(defstub q619985-zero (semiring) t)
(defstub q619985-one (semiring) t)
(defstub q619985-add (semiring left right) t)
(defstub q619985-multiply (semiring left right) t)
(defstub q619985-family-value (family index) t)

;; Exact first-order presentation of Lean's possibly trivial Semiring class.

(defun-sk q619985-semiring-laws-p (semiring)
  (forall (x y z)
    (and
     (implies
      (q619985-scalar-member-p semiring x)
      (let ((zero (q619985-zero semiring))
            (one (q619985-one semiring)))
        (and
         (equal (q619985-add semiring x zero) x)
         (equal (q619985-add semiring zero x) x)
         (equal (q619985-multiply semiring x one) x)
         (equal (q619985-multiply semiring one x) x)
         (equal (q619985-multiply semiring x zero) zero)
         (equal (q619985-multiply semiring zero x) zero))))
     (implies
      (and
       (q619985-scalar-member-p semiring x)
       (q619985-scalar-member-p semiring y))
      (and
       (q619985-scalar-member-p
        semiring
        (q619985-add semiring x y))
       (q619985-scalar-member-p
        semiring
        (q619985-multiply semiring x y))
       (equal
        (q619985-add semiring x y)
        (q619985-add semiring y x))))
     (implies
      (and
       (q619985-scalar-member-p semiring x)
       (q619985-scalar-member-p semiring y)
       (q619985-scalar-member-p semiring z))
      (and
       (equal
        (q619985-add
         semiring
         (q619985-add semiring x y)
         z)
        (q619985-add
         semiring
         x
         (q619985-add semiring y z)))
       (equal
        (q619985-multiply
         semiring
         (q619985-multiply semiring x y)
         z)
        (q619985-multiply
         semiring
         x
         (q619985-multiply semiring y z)))
       (equal
        (q619985-multiply
         semiring
         x
         (q619985-add semiring y z))
        (q619985-add
         semiring
         (q619985-multiply semiring x y)
         (q619985-multiply semiring x z)))
       (equal
        (q619985-multiply
         semiring
         (q619985-add semiring x y)
         z)
        (q619985-add
         semiring
         (q619985-multiply semiring x z)
         (q619985-multiply semiring y z))))))))

(defun q619985-semiring-p (semiring)
  (and
   (q619985-scalar-member-p
    semiring
    (q619985-zero semiring))
   (q619985-scalar-member-p
    semiring
    (q619985-one semiring))
   (q619985-semiring-laws-p semiring)))

(defun-sk q619985-family-p (index-type semiring family)
  (forall (index)
    (implies
     (q619985-index-member-p index-type index)
     (q619985-scalar-member-p
      semiring
      (q619985-family-value family index)))))

;; A duplicate-free true list is an enumeration of the source Finset.

(defun q619985-index-elements-p (indices index-type)
  (if (consp indices)
      (and
       (q619985-index-member-p index-type (car indices))
       (q619985-index-elements-p (cdr indices) index-type))
    (equal indices nil)))

(defun q619985-finset-p (indices index-type)
  (and
   (true-listp indices)
   (no-duplicatesp-equal indices)
   (q619985-index-elements-p indices index-type)))

(defun q619985-commutes-with-tail-p
    (semiring value tail family)
  (if (consp tail)
      (let ((next-value
             (q619985-family-value family (car tail))))
        (and
         (equal
          (q619985-multiply semiring value next-value)
          (q619985-multiply semiring next-value value))
         (q619985-commutes-with-tail-p
          semiring value (cdr tail) family)))
    (equal tail nil)))

(defun q619985-pairwise-commuting-p
    (semiring indices family)
  (if (consp indices)
      (and
       (q619985-commutes-with-tail-p
        semiring
        (q619985-family-value family (car indices))
        (cdr indices)
        family)
       (q619985-pairwise-commuting-p
        semiring (cdr indices) family))
    (equal indices nil)))

;; Semiring-valued finite sums, natural casts, powers, and ordered products.

(defun q619985-r-nat (semiring n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q619985-zero semiring)
    (q619985-add
     semiring
     (q619985-one semiring)
     (q619985-r-nat semiring (1- n)))))

(defun q619985-r-power (semiring base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q619985-one semiring)
    (q619985-multiply
     semiring
     base
     (q619985-r-power semiring base (1- exponent)))))

(defun q619985-sum-values (semiring indices family)
  (if (consp indices)
      (q619985-add
       semiring
       (q619985-family-value family (car indices))
       (q619985-sum-values semiring (cdr indices) family))
    (q619985-zero semiring)))

(defun q619985-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (q619985-factorial (1- n)))))

(defun q619985-sum-naturals (values)
  (if (consp values)
      (+ (nfix (car values))
         (q619985-sum-naturals (cdr values)))
    0))

(defun q619985-product-factorials (values)
  (if (consp values)
      (* (q619985-factorial (nfix (car values)))
         (q619985-product-factorials (cdr values)))
    1))

(defun q619985-multinomial-coefficient (exponents)
  (floor
   (q619985-factorial
    (q619985-sum-naturals exponents))
   (q619985-product-factorials exponents)))

;; For a list of length |s|, these are exactly the tuples in {0,...,n}^|s|.
;; Filtering by total n below gives a bijective list presentation of
;; Finset.piAntidiag s n, including the empty-set cases.

(defun q619985-range-down (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list 0)
    (cons n (q619985-range-down (1- n)))))

(defun q619985-prepend-to-tuples (value tuples)
  (if (consp tuples)
      (cons
       (cons value (car tuples))
       (q619985-prepend-to-tuples value (cdr tuples)))
    nil))

(defun q619985-prepend-values-to-tuples (values tuples)
  (if (consp values)
      (append
       (q619985-prepend-to-tuples (car values) tuples)
       (q619985-prepend-values-to-tuples (cdr values) tuples))
    nil))

(defun q619985-exponent-tuples (count n)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (list nil)
    (q619985-prepend-values-to-tuples
     (q619985-range-down n)
     (q619985-exponent-tuples (1- count) n))))

(defun q619985-noncomm-monomial
    (semiring indices exponents family)
  (if (and (consp indices) (consp exponents))
      (q619985-multiply
       semiring
       (q619985-r-power
        semiring
        (q619985-family-value family (car indices))
        (car exponents))
       (q619985-noncomm-monomial
        semiring (cdr indices) (cdr exponents) family))
    (q619985-one semiring)))

(defun q619985-multinomial-term
    (semiring indices exponents family)
  (q619985-multiply
   semiring
   (q619985-r-nat
    semiring
    (q619985-multinomial-coefficient exponents))
   (q619985-noncomm-monomial
    semiring indices exponents family)))

(defun q619985-multinomial-sum
    (semiring tuples indices n family)
  (if (consp tuples)
      (if (equal (q619985-sum-naturals (car tuples)) n)
          (q619985-add
           semiring
           (q619985-multinomial-term
            semiring indices (car tuples) family)
           (q619985-multinomial-sum
            semiring (cdr tuples) indices n family))
        (q619985-multinomial-sum
         semiring (cdr tuples) indices n family))
    (q619985-zero semiring)))

(defun thousand-theorems-q619985-multinomial-theorem-statement
    (index-type semiring family indices n)
  (implies
   (and
    (q619985-semiring-p semiring)
    (q619985-family-p index-type semiring family)
    (q619985-finset-p indices index-type)
    (q619985-pairwise-commuting-p
     semiring indices family)
    (natp n))
   (equal
    (q619985-r-power
     semiring
     (q619985-sum-values semiring indices family)
     n)
    (q619985-multinomial-sum
     semiring
     (q619985-exponent-tuples (len indices) n)
     indices
     n
     family))))

(value-triple :itpeval-statement-checked)
:q
