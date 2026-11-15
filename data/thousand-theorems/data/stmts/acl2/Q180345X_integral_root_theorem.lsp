;; Statement-only formalization of thousand-theorems corpus artifact Q180345X,
;; "Integral root theorem": over an arbitrary unique factorization domain and
;; its fraction field, every root of a monic polynomial lies in the image of
;; the domain's canonical embedding. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative function symbols present arbitrary, potentially infinite
;; carriers and their operations, indexed by structure identifiers. The
;; declarations supply no algebraic laws: every ring, domain, field,
;; embedding, and fraction-field condition is stated explicitly below with
;; direct DEFUN-SK quantifiers.
;;
;; A UFD is presented by the equivalent characterization that every nonzero
;; element is a unit times a finite product of prime elements. Polynomials are
;; canonical ascending coefficient lists: NIL is zero, and a nonempty list has
;; nonzero final coefficient. Thus they are exactly finite-support univariate
;; polynomials, with no degree bound. Being an integer means that an internally
;; quantified domain element maps to the given fraction-field element.

(defstub q180345x-element-p (structure value) t)
(defstub q180345x-zero (structure) t)
(defstub q180345x-one (structure) t)
(defstub q180345x-add (structure left right) t)
(defstub q180345x-multiply (structure left right) t)
(defstub q180345x-negate (structure value) t)
(defstub q180345x-inverse (structure value) t)
(defstub q180345x-embed
  (small-structure large-structure value)
  t)

;; Commutative rings and integral domains.

(defun-sk q180345x-commutative-ring-laws-p (structure)
  (forall (x y z)
    (implies
     (and
      (q180345x-element-p structure x)
      (q180345x-element-p structure y)
      (q180345x-element-p structure z))
     (let* ((zero (q180345x-zero structure))
            (one (q180345x-one structure))
            (x-plus-y (q180345x-add structure x y))
            (y-plus-z (q180345x-add structure y z))
            (x-times-y (q180345x-multiply structure x y))
            (y-times-z (q180345x-multiply structure y z))
            (negative-x (q180345x-negate structure x)))
       (and
        (q180345x-element-p structure x-plus-y)
        (q180345x-element-p structure x-times-y)
        (q180345x-element-p structure negative-x)
        (equal
         (q180345x-add structure x-plus-y z)
         (q180345x-add structure x y-plus-z))
        (equal x-plus-y (q180345x-add structure y x))
        (equal (q180345x-add structure x zero) x)
        (equal (q180345x-add structure x negative-x) zero)
        (equal
         (q180345x-multiply structure x-times-y z)
         (q180345x-multiply structure x y-times-z))
        (equal x-times-y (q180345x-multiply structure y x))
        (equal (q180345x-multiply structure x one) x)
        (equal
         (q180345x-multiply structure x y-plus-z)
         (q180345x-add
          structure
          (q180345x-multiply structure x y)
          (q180345x-multiply structure x z))))))))

(defun-sk q180345x-no-zero-divisors-p (structure)
  (forall (x y)
    (implies
     (and
      (q180345x-element-p structure x)
      (q180345x-element-p structure y)
      (equal
       (q180345x-multiply structure x y)
       (q180345x-zero structure)))
     (or
      (equal x (q180345x-zero structure))
      (equal y (q180345x-zero structure))))))

(defun q180345x-integral-domain-p (structure)
  (and
   (q180345x-element-p structure (q180345x-zero structure))
   (q180345x-element-p structure (q180345x-one structure))
   (not
    (equal
     (q180345x-zero structure)
     (q180345x-one structure)))
   (q180345x-commutative-ring-laws-p structure)
   (q180345x-no-zero-divisors-p structure)))

;; Units, divisibility, primes, and the UFD factorization property.

(defun-sk q180345x-unit-p (structure object)
  (exists (inverse)
    (and
     (q180345x-element-p structure object)
     (q180345x-element-p structure inverse)
     (equal
      (q180345x-multiply structure object inverse)
      (q180345x-one structure)))))

(defun-sk q180345x-divides-p
    (structure divisor dividend)
  (exists (quotient)
    (and
     (q180345x-element-p structure divisor)
     (q180345x-element-p structure dividend)
     (q180345x-element-p structure quotient)
     (equal
      (q180345x-multiply structure divisor quotient)
      dividend))))

(defun-sk q180345x-prime-divisor-law-p
    (structure prime)
  (forall (x y)
    (implies
     (and
      (q180345x-element-p structure x)
      (q180345x-element-p structure y)
      (q180345x-divides-p
       structure
       prime
       (q180345x-multiply structure x y)))
     (or
      (q180345x-divides-p structure prime x)
      (q180345x-divides-p structure prime y)))))

(defun q180345x-prime-p (structure object)
  (and
   (q180345x-element-p structure object)
   (not (equal object (q180345x-zero structure)))
   (not (q180345x-unit-p structure object))
   (q180345x-prime-divisor-law-p structure object)))

(defun q180345x-prime-list-p (structure factors)
  (if (consp factors)
      (and
       (q180345x-prime-p structure (car factors))
       (q180345x-prime-list-p structure (cdr factors)))
    (equal factors nil)))

(defun q180345x-product (structure factors)
  (if (consp factors)
      (q180345x-multiply
       structure
       (car factors)
       (q180345x-product structure (cdr factors)))
    (q180345x-one structure)))

(defun-sk q180345x-associates-p
    (structure left right)
  (exists (unit)
    (and
     (q180345x-element-p structure left)
     (q180345x-element-p structure right)
     (q180345x-unit-p structure unit)
     (equal
      (q180345x-multiply structure unit right)
      left))))

(defun q180345x-factorization-p
    (structure object factors)
  (and
   (true-listp factors)
   (q180345x-prime-list-p structure factors)
   (q180345x-associates-p
    structure
    object
    (q180345x-product structure factors))))

(defun-sk q180345x-factorization-exists-p
    (structure object)
  (exists (factors)
    (q180345x-factorization-p structure object factors)))

(defun-sk q180345x-ufd-factorization-law-p (structure)
  (forall (object)
    (implies
     (and
      (q180345x-element-p structure object)
      (not (equal object (q180345x-zero structure))))
     (q180345x-factorization-exists-p structure object))))

(defun q180345x-unique-factorization-domain-p (structure)
  (and
   (q180345x-integral-domain-p structure)
   (q180345x-ufd-factorization-law-p structure)))

;; Fields, embeddings, and fraction-field presentations.

(defun-sk q180345x-field-inverse-laws-p (structure)
  (forall (x)
    (implies
     (q180345x-element-p structure x)
     (let ((inverse-x (q180345x-inverse structure x)))
       (and
        (q180345x-element-p structure inverse-x)
        (implies
         (equal x (q180345x-zero structure))
         (equal inverse-x (q180345x-zero structure)))
        (implies
         (not (equal x (q180345x-zero structure)))
         (equal
          (q180345x-multiply structure x inverse-x)
          (q180345x-one structure))))))))

(defun q180345x-field-p (structure)
  (and
   (q180345x-integral-domain-p structure)
   (q180345x-field-inverse-laws-p structure)))

(defun-sk q180345x-embedding-laws-p
    (small-structure large-structure)
  (forall (x y)
    (implies
     (and
      (q180345x-element-p small-structure x)
      (q180345x-element-p small-structure y))
     (let ((map-x
            (q180345x-embed
             small-structure large-structure x))
           (map-y
            (q180345x-embed
             small-structure large-structure y)))
       (and
        (q180345x-element-p large-structure map-x)
        (equal
         (q180345x-embed
          small-structure
          large-structure
          (q180345x-add small-structure x y))
         (q180345x-add large-structure map-x map-y))
        (equal
         (q180345x-embed
          small-structure
          large-structure
          (q180345x-multiply small-structure x y))
         (q180345x-multiply large-structure map-x map-y))
        (equal
         (q180345x-embed
          small-structure
          large-structure
          (q180345x-zero small-structure))
         (q180345x-zero large-structure))
        (equal
         (q180345x-embed
          small-structure
          large-structure
          (q180345x-one small-structure))
         (q180345x-one large-structure))
        (implies
         (equal map-x map-y)
         (equal x y)))))))

(defun-sk q180345x-fraction-exists-p
    (small-structure large-structure element)
  (exists (numerator denominator)
    (and
     (q180345x-element-p small-structure numerator)
     (q180345x-element-p small-structure denominator)
     (not
      (equal
       denominator
       (q180345x-zero small-structure)))
     (equal
      (q180345x-multiply
       large-structure
       element
       (q180345x-embed
        small-structure large-structure denominator))
      (q180345x-embed
       small-structure large-structure numerator)))))

(defun-sk q180345x-fraction-surjectivity-p
    (small-structure large-structure)
  (forall (element)
    (implies
     (q180345x-element-p large-structure element)
     (q180345x-fraction-exists-p
      small-structure large-structure element))))

(defun q180345x-fraction-field-p
    (small-structure large-structure)
  (and
   (q180345x-field-p large-structure)
   (q180345x-embedding-laws-p
    small-structure large-structure)
   (q180345x-fraction-surjectivity-p
    small-structure large-structure)))

;; Canonical univariate polynomials and evaluation through the embedding.

(defun q180345x-coefficient-list-p
    (structure coefficients)
  (if (consp coefficients)
      (and
       (q180345x-element-p structure (car coefficients))
       (q180345x-coefficient-list-p
        structure (cdr coefficients)))
    (equal coefficients nil)))

(defun q180345x-polynomial-p (structure polynomial)
  (and
   (true-listp polynomial)
   (q180345x-coefficient-list-p structure polynomial)
   (or
    (equal polynomial nil)
    (not
     (equal
      (car (last polynomial))
      (q180345x-zero structure))))))

(defun q180345x-polynomial-eval
    (small-structure large-structure polynomial root)
  (if (consp polynomial)
      (q180345x-add
       large-structure
       (q180345x-embed
        small-structure large-structure (car polynomial))
       (q180345x-multiply
        large-structure
        root
        (q180345x-polynomial-eval
         small-structure
         large-structure
         (cdr polynomial)
         root)))
    (q180345x-zero large-structure)))

(defun q180345x-leading-coefficient
    (structure polynomial)
  (if (consp polynomial)
      (car (last polynomial))
    (q180345x-zero structure)))

(defun-sk q180345x-integer-p
    (small-structure large-structure root)
  (exists (integer)
    (and
     (q180345x-element-p small-structure integer)
     (equal
      root
      (q180345x-embed
       small-structure large-structure integer)))))

(defun-sk
    thousand-theorems-q180345x-integral-root-theorem-statement
    ()
  (forall (small-structure large-structure polynomial root)
    (implies
     (and
      (q180345x-unique-factorization-domain-p
       small-structure)
      (q180345x-fraction-field-p
       small-structure large-structure)
      (q180345x-polynomial-p small-structure polynomial)
      (equal
       (q180345x-leading-coefficient
        small-structure polynomial)
       (q180345x-one small-structure))
      (q180345x-element-p large-structure root)
      (equal
       (q180345x-polynomial-eval
        small-structure large-structure polynomial root)
       (q180345x-zero large-structure)))
     (q180345x-integer-p
      small-structure large-structure root))))

(value-triple :itpeval-statement-checked)
:q
