;; Statement-only formalization of thousand-theorems corpus artifact Q180345,
;; "Rational root theorem": over an arbitrary unique factorization domain and
;; its fraction field, a polynomial root's reduced numerator divides the
;; constant coefficient and its reduced denominator divides the leading
;; coefficient. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative stubs represent arbitrary carrier predicates, constants,
;; operations, the fraction-field embedding, and reduced numerator and
;; denominator selectors. Every required algebraic and representation law is
;; explicit below; the stubs themselves supply no assumptions.

(defstub q180345-a-p (x) t)
(defstub q180345-a-zero () t)
(defstub q180345-a-one () t)
(defstub q180345-a-add (x y) t)
(defstub q180345-a-mul (x y) t)
(defstub q180345-a-neg (x) t)

(defstub q180345-k-p (x) t)
(defstub q180345-k-zero () t)
(defstub q180345-k-one () t)
(defstub q180345-k-add (x y) t)
(defstub q180345-k-mul (x y) t)
(defstub q180345-k-neg (x) t)
(defstub q180345-k-inv (x) t)

(defstub q180345-embed (x) t)
(defstub q180345-num (x) t)
(defstub q180345-den (x) t)

;; A commutative integral domain.

(defun-sk q180345-a-ring-laws-p ()
  (forall
   (x y z)
   (implies
    (and (q180345-a-p x)
         (q180345-a-p y)
         (q180345-a-p z))
    (and
     (q180345-a-p (q180345-a-add x y))
     (q180345-a-p (q180345-a-mul x y))
     (q180345-a-p (q180345-a-neg x))
     (equal
      (q180345-a-add (q180345-a-add x y) z)
      (q180345-a-add x (q180345-a-add y z)))
     (equal (q180345-a-add x y)
            (q180345-a-add y x))
     (equal (q180345-a-add x (q180345-a-zero))
            x)
     (equal (q180345-a-add x (q180345-a-neg x))
            (q180345-a-zero))
     (equal
      (q180345-a-mul (q180345-a-mul x y) z)
      (q180345-a-mul x (q180345-a-mul y z)))
     (equal (q180345-a-mul x y)
            (q180345-a-mul y x))
     (equal (q180345-a-mul x (q180345-a-one))
            x)
     (equal
      (q180345-a-mul x (q180345-a-add y z))
      (q180345-a-add
       (q180345-a-mul x y)
       (q180345-a-mul x z)))))))

(defun-sk q180345-a-no-zero-divisors-p ()
  (forall
   (x y)
   (implies
    (and (q180345-a-p x)
         (q180345-a-p y)
         (equal (q180345-a-mul x y)
                (q180345-a-zero)))
    (or (equal x (q180345-a-zero))
        (equal y (q180345-a-zero))))))

(defun q180345-a-integral-domain-p ()
  (and
   (q180345-a-p (q180345-a-zero))
   (q180345-a-p (q180345-a-one))
   (not (equal (q180345-a-zero)
               (q180345-a-one)))
   (q180345-a-ring-laws-p)
   (q180345-a-no-zero-divisors-p)))

;; Units, divisibility, prime elements, and the UFD factorization condition.

(defun-sk q180345-unit-p (object)
  (exists
   (inverse)
   (and
    (q180345-a-p object)
    (q180345-a-p inverse)
    (equal (q180345-a-mul object inverse)
           (q180345-a-one)))))

(defun-sk q180345-divides-p (divisor dividend)
  (exists
   (quotient)
   (and
    (q180345-a-p divisor)
    (q180345-a-p dividend)
    (q180345-a-p quotient)
    (equal (q180345-a-mul divisor quotient)
           dividend))))

(defun-sk q180345-prime-divisor-law-p (prime)
  (forall
   (x y)
   (implies
    (and
     (q180345-a-p x)
     (q180345-a-p y)
     (q180345-divides-p
      prime
      (q180345-a-mul x y)))
    (or (q180345-divides-p prime x)
        (q180345-divides-p prime y)))))

(defun q180345-prime-p (object)
  (and
   (q180345-a-p object)
   (not (equal object (q180345-a-zero)))
   (not (q180345-unit-p object))
   (q180345-prime-divisor-law-p object)))

(defun q180345-prime-list-p (factors)
  (if (consp factors)
      (and
       (q180345-prime-p (car factors))
       (q180345-prime-list-p (cdr factors)))
    (equal factors nil)))

(defun q180345-product (factors)
  (if (consp factors)
      (q180345-a-mul
       (car factors)
       (q180345-product (cdr factors)))
    (q180345-a-one)))

(defun-sk q180345-associates-p (left right)
  (exists
   (unit)
   (and
    (q180345-a-p left)
    (q180345-a-p right)
    (q180345-unit-p unit)
    (equal (q180345-a-mul unit right)
           left))))

(defun q180345-factorization-p (object factors)
  (and
   (true-listp factors)
   (q180345-prime-list-p factors)
   (q180345-associates-p
    object
    (q180345-product factors))))

(defun-sk q180345-factorization-exists-p (object)
  (exists
   (factors)
   (q180345-factorization-p object factors)))

(defun-sk q180345-every-nonzero-factors-p ()
  (forall
   (object)
   (implies
    (and
     (q180345-a-p object)
     (not (equal object (q180345-a-zero))))
    (q180345-factorization-exists-p object))))

;; In an integral domain, existence of finite factorizations into prime
;; elements is equivalent to unique factorization.
(defun q180345-unique-factorization-domain-p ()
  (and
   (q180345-a-integral-domain-p)
   (q180345-every-nonzero-factors-p)))

;; A field K, an injective ring embedding A -> K, and the condition that every
;; element of K is represented by a quotient of elements of A.

(defun-sk q180345-k-field-laws-p ()
  (forall
   (x y z)
   (implies
    (and (q180345-k-p x)
         (q180345-k-p y)
         (q180345-k-p z))
    (and
     (q180345-k-p (q180345-k-add x y))
     (q180345-k-p (q180345-k-mul x y))
     (q180345-k-p (q180345-k-neg x))
     (q180345-k-p (q180345-k-inv x))
     (equal
      (q180345-k-add (q180345-k-add x y) z)
      (q180345-k-add x (q180345-k-add y z)))
     (equal (q180345-k-add x y)
            (q180345-k-add y x))
     (equal (q180345-k-add x (q180345-k-zero))
            x)
     (equal (q180345-k-add x (q180345-k-neg x))
            (q180345-k-zero))
     (equal
      (q180345-k-mul (q180345-k-mul x y) z)
      (q180345-k-mul x (q180345-k-mul y z)))
     (equal (q180345-k-mul x y)
            (q180345-k-mul y x))
     (equal (q180345-k-mul x (q180345-k-one))
            x)
     (equal
      (q180345-k-mul x (q180345-k-add y z))
      (q180345-k-add
       (q180345-k-mul x y)
       (q180345-k-mul x z)))
     (implies
      (equal x (q180345-k-zero))
      (equal (q180345-k-inv x)
             (q180345-k-zero)))
     (implies
      (not (equal x (q180345-k-zero)))
      (equal (q180345-k-mul x (q180345-k-inv x))
             (q180345-k-one)))))))

(defun-sk q180345-k-no-zero-divisors-p ()
  (forall
   (x y)
   (implies
    (and (q180345-k-p x)
         (q180345-k-p y)
         (equal (q180345-k-mul x y)
                (q180345-k-zero)))
    (or (equal x (q180345-k-zero))
        (equal y (q180345-k-zero))))))

(defun q180345-field-p ()
  (and
   (q180345-k-p (q180345-k-zero))
   (q180345-k-p (q180345-k-one))
   (not (equal (q180345-k-zero)
               (q180345-k-one)))
   (q180345-k-field-laws-p)
   (q180345-k-no-zero-divisors-p)))

(defun-sk q180345-embedding-laws-p ()
  (forall
   (x y)
   (implies
    (and (q180345-a-p x)
         (q180345-a-p y))
    (and
     (q180345-k-p (q180345-embed x))
     (q180345-k-p (q180345-embed y))
     (equal
      (q180345-embed (q180345-a-add x y))
      (q180345-k-add
       (q180345-embed x)
       (q180345-embed y)))
     (equal
      (q180345-embed (q180345-a-mul x y))
      (q180345-k-mul
       (q180345-embed x)
       (q180345-embed y)))
     (equal
      (q180345-embed (q180345-a-neg x))
      (q180345-k-neg (q180345-embed x)))
     (implies
      (equal (q180345-embed x)
             (q180345-embed y))
      (equal x y))))))

(defun q180345-embedding-p ()
  (and
   (equal (q180345-embed (q180345-a-zero))
          (q180345-k-zero))
   (equal (q180345-embed (q180345-a-one))
          (q180345-k-one))
   (q180345-embedding-laws-p)))

(defun-sk q180345-fraction-representable-p (element)
  (exists
   (numerator denominator)
   (and
    (q180345-a-p numerator)
    (q180345-a-p denominator)
    (not (equal denominator (q180345-a-zero)))
    (equal
     (q180345-k-mul
      element
      (q180345-embed denominator))
     (q180345-embed numerator)))))

(defun-sk q180345-every-field-element-is-fraction-p ()
  (forall
   (element)
   (implies
    (q180345-k-p element)
    (q180345-fraction-representable-p element))))

(defun q180345-fraction-field-p ()
  (and
   (q180345-field-p)
   (q180345-embedding-p)
   (q180345-every-field-element-is-fraction-p)))

;; Reduced numerator and denominator selectors. Any two reduced presentations
;; differ by multiplication by a unit, so the two divisibility conclusions
;; are invariant under this target-native choice.

(defun-sk q180345-common-divisors-are-units-p (left right)
  (forall
   (divisor)
   (implies
    (and
     (q180345-a-p divisor)
     (q180345-divides-p divisor left)
     (q180345-divides-p divisor right))
    (q180345-unit-p divisor))))

(defun q180345-coprime-p (left right)
  (and
   (q180345-a-p left)
   (q180345-a-p right)
   (q180345-common-divisors-are-units-p left right)))

(defun-sk q180345-reduced-fraction-presentation-p ()
  (forall
   (element)
   (implies
    (q180345-k-p element)
    (and
     (q180345-a-p (q180345-num element))
     (q180345-a-p (q180345-den element))
     (not
      (equal (q180345-den element)
             (q180345-a-zero)))
     (equal
      (q180345-k-mul
       element
       (q180345-embed (q180345-den element)))
      (q180345-embed (q180345-num element)))
     (q180345-coprime-p
      (q180345-num element)
      (q180345-den element))))))

;; Canonical ascending coefficient lists are exactly finite-support
;; univariate polynomials: NIL is zero and a nonempty list has a nonzero final
;; coefficient.

(defun q180345-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (q180345-a-p (car coefficients))
       (q180345-coefficient-list-p (cdr coefficients)))
    (equal coefficients nil)))

(defun q180345-polynomial-p (polynomial)
  (and
   (true-listp polynomial)
   (q180345-coefficient-list-p polynomial)
   (or
    (equal polynomial nil)
    (not
     (equal (car (last polynomial))
            (q180345-a-zero))))))

(defun q180345-polynomial-eval (polynomial root)
  (if (consp polynomial)
      (q180345-k-add
       (q180345-embed (car polynomial))
       (q180345-k-mul
        root
        (q180345-polynomial-eval
         (cdr polynomial)
         root)))
    (q180345-k-zero)))

(defun q180345-constant-coefficient (polynomial)
  (if (consp polynomial)
      (car polynomial)
    (q180345-a-zero)))

(defun q180345-leading-coefficient (polynomial)
  (if (consp polynomial)
      (car (last polynomial))
    (q180345-a-zero)))

(defun thousand-theorems-q180345-rational-root-theorem-statement
    (polynomial root)
  (implies
   (and
    (q180345-unique-factorization-domain-p)
    (q180345-fraction-field-p)
    (q180345-reduced-fraction-presentation-p)
    (q180345-polynomial-p polynomial)
    (q180345-k-p root)
    (equal
     (q180345-polynomial-eval polynomial root)
     (q180345-k-zero)))
   (and
    (q180345-divides-p
     (q180345-num root)
     (q180345-constant-coefficient polynomial))
    (q180345-divides-p
     (q180345-den root)
     (q180345-leading-coefficient polynomial)))))

(value-triple :itpeval-statement-checked)
:q
