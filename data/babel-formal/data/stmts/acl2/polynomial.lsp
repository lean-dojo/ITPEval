;; Statement-only formalization of Babel-formal artifact polynomial: degree,
;; evaluation, linear root factors, products of roots, and the distinct-roots
;; bound over a generic commutative ring/polynomial interface with no zero
;; divisors. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent the arbitrary coefficient ring,
;; polynomial ring, degree, monomial, and evaluation operations.  Ring tags
;; select carriers and operations; an interface tag selects degree, monomial,
;; and evaluation functions.  Every typing and algebraic law is explicit in
;; the predicates below.

(defstub bf-polynomial-element-p (ring value) t)
(defstub bf-polynomial-zero (ring) t)
(defstub bf-polynomial-one (ring) t)
(defstub bf-polynomial-opp (ring value) t)
(defstub bf-polynomial-add (ring left right) t)
(defstub bf-polynomial-mul (ring left right) t)

(defstub bf-polynomial-degree (interface polynomial) t)
(defstub bf-polynomial-monomial (interface degree coefficient) t)
(defstub bf-polynomial-eval (interface polynomial coefficient) t)

(defun bf-polynomial-c (interface coefficient)
  (bf-polynomial-monomial interface 0 coefficient))

(defun bf-polynomial-x (interface coefficient-ring)
  (bf-polynomial-monomial
   interface 1 (bf-polynomial-one coefficient-ring)))

(defun bf-polynomial-x-minus
    (interface coefficient-ring polynomial-ring a)
  (bf-polynomial-add
   polynomial-ring
   (bf-polynomial-x interface coefficient-ring)
   (bf-polynomial-c
    interface (bf-polynomial-opp coefficient-ring a))))

(defun bf-polynomial-root-p
    (interface coefficient-ring polynomial a)
  (equal
   (bf-polynomial-eval interface polynomial a)
   (bf-polynomial-zero coefficient-ring)))

;; Native ACL2 naturals and proper lists are constructor-preserving encodings
;; of the source mynat and mylist datatypes.

(defun bf-polynomial-ring-list-p (ring xs)
  (if (consp xs)
      (and
       (bf-polynomial-element-p ring (car xs))
       (bf-polynomial-ring-list-p ring (cdr xs)))
    (equal xs nil)))

(defun bf-polynomial-member-p (value xs)
  (if (consp xs)
      (or
       (equal value (car xs))
       (bf-polynomial-member-p value (cdr xs)))
    nil))

(defun bf-polynomial-no-duplicates-p (xs)
  (if (consp xs)
      (and
       (not (bf-polynomial-member-p (car xs) (cdr xs)))
       (bf-polynomial-no-duplicates-p (cdr xs)))
    (equal xs nil)))

(defun bf-polynomial-poly-of-roots
    (interface coefficient-ring polynomial-ring xs)
  (if (consp xs)
      (bf-polynomial-mul
       polynomial-ring
       (bf-polynomial-x-minus
        interface coefficient-ring polynomial-ring (car xs))
       (bf-polynomial-poly-of-roots
        interface coefficient-ring polynomial-ring (cdr xs)))
    (bf-polynomial-one polynomial-ring)))

(defun-sk bf-polynomial-all-roots-p
    (interface coefficient-ring xs polynomial)
  (forall (a)
    (implies
     (and
      (bf-polynomial-element-p coefficient-ring a)
      (bf-polynomial-member-p a xs))
     (bf-polynomial-root-p
      interface coefficient-ring polynomial a))))

;; The source ring class is a commutative ring with one distinct from zero and
;; no zero divisors.  Closure conditions make the source typing explicit in
;; ACL2's untyped logic.

(defun-sk bf-polynomial-ring-laws-p (ring)
  (forall (x y z)
    (and
     (implies
      (bf-polynomial-element-p ring x)
      (and
       (bf-polynomial-element-p
        ring (bf-polynomial-opp ring x))
       (equal
        (bf-polynomial-add
         ring x (bf-polynomial-zero ring))
        x)
       (equal
        (bf-polynomial-add
         ring x (bf-polynomial-opp ring x))
        (bf-polynomial-zero ring))
       (equal
        (bf-polynomial-mul
         ring x (bf-polynomial-one ring))
        x)
       (equal
        (bf-polynomial-mul
         ring x (bf-polynomial-zero ring))
        (bf-polynomial-zero ring))))
     (implies
      (and
       (bf-polynomial-element-p ring x)
       (bf-polynomial-element-p ring y))
      (and
       (bf-polynomial-element-p
        ring (bf-polynomial-add ring x y))
       (bf-polynomial-element-p
        ring (bf-polynomial-mul ring x y))
       (equal
        (bf-polynomial-add ring x y)
        (bf-polynomial-add ring y x))
       (equal
        (bf-polynomial-mul ring x y)
        (bf-polynomial-mul ring y x))
       (implies
        (equal
         (bf-polynomial-mul ring x y)
         (bf-polynomial-zero ring))
        (or
         (equal x (bf-polynomial-zero ring))
         (equal y (bf-polynomial-zero ring))))))
     (implies
      (and
       (bf-polynomial-element-p ring x)
       (bf-polynomial-element-p ring y)
       (bf-polynomial-element-p ring z))
      (and
       (equal
        (bf-polynomial-add
         ring (bf-polynomial-add ring x y) z)
        (bf-polynomial-add
         ring x (bf-polynomial-add ring y z)))
       (equal
        (bf-polynomial-mul
         ring (bf-polynomial-mul ring x y) z)
        (bf-polynomial-mul
         ring x (bf-polynomial-mul ring y z)))
       (equal
        (bf-polynomial-mul
         ring x (bf-polynomial-add ring y z))
        (bf-polynomial-add
         ring
         (bf-polynomial-mul ring x y)
         (bf-polynomial-mul ring x z))))))))

(defun bf-polynomial-ring-p (ring)
  (and
   (bf-polynomial-element-p
    ring (bf-polynomial-zero ring))
   (bf-polynomial-element-p
    ring (bf-polynomial-one ring))
   (not
    (equal
     (bf-polynomial-one ring)
     (bf-polynomial-zero ring)))
   (bf-polynomial-ring-laws-p ring)))

;; These helpers retain the source existential quantifiers used by the
;; degree-zero characterization and division by a linear factor.

(defun-sk bf-polynomial-constant-representation-p
    (interface coefficient-ring polynomial)
  (exists (coefficient)
    (and
     (bf-polynomial-element-p coefficient-ring coefficient)
     (equal
      polynomial
      (bf-polynomial-c interface coefficient)))))

(defun-sk bf-polynomial-linear-division-p
    (interface coefficient-ring polynomial-ring polynomial a)
  (exists (quotient remainder)
    (and
     (bf-polynomial-element-p polynomial-ring quotient)
     (bf-polynomial-element-p polynomial-ring remainder)
     (equal
      polynomial
      (bf-polynomial-add
       polynomial-ring
       (bf-polynomial-mul
        polynomial-ring
        quotient
        (bf-polynomial-x-minus
         interface coefficient-ring polynomial-ring a))
       remainder))
     (equal
      (bf-polynomial-degree interface remainder)
      0))))

(defun-sk bf-polynomial-monomial-closure-p
    (interface coefficient-ring polynomial-ring)
  (forall (n c)
    (implies
     (and
      (natp n)
      (bf-polynomial-element-p coefficient-ring c))
     (bf-polynomial-element-p
      polynomial-ring
      (bf-polynomial-monomial interface n c)))))

(defun-sk bf-polynomial-degree-closure-p
    (interface polynomial-ring)
  (forall (p)
    (implies
     (bf-polynomial-element-p polynomial-ring p)
     (natp (bf-polynomial-degree interface p)))))

(defun-sk bf-polynomial-eval-closure-p
    (interface coefficient-ring polynomial-ring)
  (forall (p x)
    (implies
     (and
      (bf-polynomial-element-p polynomial-ring p)
      (bf-polynomial-element-p coefficient-ring x))
     (bf-polynomial-element-p
      coefficient-ring
      (bf-polynomial-eval interface p x)))))

(defun-sk bf-polynomial-eval-add-law-p
    (interface coefficient-ring polynomial-ring)
  (forall (p q x)
    (implies
     (and
      (bf-polynomial-element-p polynomial-ring p)
      (bf-polynomial-element-p polynomial-ring q)
      (bf-polynomial-element-p coefficient-ring x))
     (equal
      (bf-polynomial-eval
       interface
       (bf-polynomial-add polynomial-ring p q)
       x)
      (bf-polynomial-add
       coefficient-ring
       (bf-polynomial-eval interface p x)
       (bf-polynomial-eval interface q x))))))

(defun-sk bf-polynomial-eval-mul-law-p
    (interface coefficient-ring polynomial-ring)
  (forall (p q x)
    (implies
     (and
      (bf-polynomial-element-p polynomial-ring p)
      (bf-polynomial-element-p polynomial-ring q)
      (bf-polynomial-element-p coefficient-ring x))
     (equal
      (bf-polynomial-eval
       interface
       (bf-polynomial-mul polynomial-ring p q)
       x)
      (bf-polynomial-mul
       coefficient-ring
       (bf-polynomial-eval interface p x)
       (bf-polynomial-eval interface q x))))))

(defun-sk bf-polynomial-eval-c-law-p
    (interface coefficient-ring)
  (forall (c x)
    (implies
     (and
      (bf-polynomial-element-p coefficient-ring c)
      (bf-polynomial-element-p coefficient-ring x))
     (equal
      (bf-polynomial-eval
       interface (bf-polynomial-c interface c) x)
      c))))

(defun-sk bf-polynomial-eval-x-law-p
    (interface coefficient-ring)
  (forall (x)
    (implies
     (bf-polynomial-element-p coefficient-ring x)
     (equal
      (bf-polynomial-eval
       interface
       (bf-polynomial-x interface coefficient-ring)
       x)
      x))))

(defun-sk bf-polynomial-deg-c-law-p
    (interface coefficient-ring)
  (forall (c)
    (implies
     (and
      (bf-polynomial-element-p coefficient-ring c)
      (not
       (equal c (bf-polynomial-zero coefficient-ring))))
     (equal
      (bf-polynomial-degree
       interface (bf-polynomial-c interface c))
      0))))

(defun-sk bf-polynomial-deg-constant-law-p
    (interface coefficient-ring polynomial-ring)
  (forall (p)
    (implies
     (bf-polynomial-element-p polynomial-ring p)
     (iff
      (equal (bf-polynomial-degree interface p) 0)
      (bf-polynomial-constant-representation-p
       interface coefficient-ring p)))))

(defun-sk bf-polynomial-deg-x-minus-law-p
    (interface coefficient-ring polynomial-ring)
  (forall (a)
    (implies
     (bf-polynomial-element-p coefficient-ring a)
     (equal
      (bf-polynomial-degree
       interface
       (bf-polynomial-x-minus
        interface coefficient-ring polynomial-ring a))
      1))))

(defun-sk bf-polynomial-deg-mul-law-p
    (interface polynomial-ring)
  (forall (p q)
    (implies
     (and
      (bf-polynomial-element-p polynomial-ring p)
      (bf-polynomial-element-p polynomial-ring q)
      (not
       (equal p (bf-polynomial-zero polynomial-ring)))
      (not
       (equal q (bf-polynomial-zero polynomial-ring))))
     (equal
      (bf-polynomial-degree
       interface
       (bf-polynomial-mul polynomial-ring p q))
      (+
       (bf-polynomial-degree interface p)
       (bf-polynomial-degree interface q))))))

(defun-sk bf-polynomial-linear-division-law-p
    (interface coefficient-ring polynomial-ring)
  (forall (p a)
    (implies
     (and
      (bf-polynomial-element-p polynomial-ring p)
      (bf-polynomial-element-p coefficient-ring a))
     (bf-polynomial-linear-division-p
      interface coefficient-ring polynomial-ring p a))))

(defun bf-polynomial-interface-laws-p
    (interface coefficient-ring polynomial-ring)
  (and
   (bf-polynomial-monomial-closure-p
    interface coefficient-ring polynomial-ring)
   (bf-polynomial-degree-closure-p interface polynomial-ring)
   (bf-polynomial-eval-closure-p
    interface coefficient-ring polynomial-ring)
   (bf-polynomial-eval-add-law-p
    interface coefficient-ring polynomial-ring)
   (bf-polynomial-eval-mul-law-p
    interface coefficient-ring polynomial-ring)
   (bf-polynomial-eval-c-law-p interface coefficient-ring)
   (bf-polynomial-eval-x-law-p interface coefficient-ring)
   (bf-polynomial-deg-c-law-p interface coefficient-ring)
   (bf-polynomial-deg-constant-law-p
    interface coefficient-ring polynomial-ring)
   (bf-polynomial-deg-x-minus-law-p
    interface coefficient-ring polynomial-ring)
   (bf-polynomial-deg-mul-law-p interface polynomial-ring)
   (bf-polynomial-linear-division-law-p
    interface coefficient-ring polynomial-ring)))

(defun bf-polynomial-context-p
    (interface coefficient-ring polynomial-ring)
  (and
   (bf-polynomial-ring-p coefficient-ring)
   (bf-polynomial-ring-p polynomial-ring)
   (equal
    (bf-polynomial-c
     interface (bf-polynomial-zero coefficient-ring))
    (bf-polynomial-zero polynomial-ring))
   (equal
    (bf-polynomial-c
     interface (bf-polynomial-one coefficient-ring))
    (bf-polynomial-one polynomial-ring))
   (equal
    (bf-polynomial-degree
     interface (bf-polynomial-zero polynomial-ring))
    0)
   (bf-polynomial-interface-laws-p
    interface coefficient-ring polynomial-ring)))

;; Statements for the source's custom-natural-number infrastructure.

(defun-sk bf-polynomial-mynat-add-o-left-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal (+ 0 m) m))))

(defun-sk bf-polynomial-mynat-add-s-left-statement ()
  (forall (n m)
    (implies
     (and (natp n) (natp m))
     (equal
      (+ (+ 1 n) m)
      (+ 1 (+ n m))))))

(defun-sk bf-polynomial-mynat-zero-le-statement ()
  (forall (n)
    (implies
     (natp n)
     (<= 0 n))))

(defun-sk bf-polynomial-mynat-add-zero-r-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal (+ n 0) n))))

(defun-sk bf-polynomial-mynat-succ-le-succ-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (<= n m))
     (<= (+ 1 n) (+ 1 m)))))

(defun-sk bf-polynomial-mynat-add-s-r-statement ()
  (forall (m n)
    (implies
     (and (natp m) (natp n))
     (equal
      (+ m (+ 1 n))
      (+ 1 (+ m n))))))

(defun-sk bf-polynomial-mynat-add-comm-statement ()
  (forall (n m)
    (implies
     (and (natp n) (natp m))
     (equal (+ n m) (+ m n)))))

;; Derived polynomial statements.  Each theorem keeps the complete generic
;; context as an explicit antecedent.

(defun-sk bf-polynomial-sub-eq-zero-l-statement ()
  (forall (coefficient-ring a b)
    (implies
     (and
      (bf-polynomial-ring-p coefficient-ring)
      (bf-polynomial-element-p coefficient-ring a)
      (bf-polynomial-element-p coefficient-ring b)
      (equal
       (bf-polynomial-add
        coefficient-ring
        a
        (bf-polynomial-opp coefficient-ring b))
       (bf-polynomial-zero coefficient-ring)))
     (equal a b))))

(defun-sk bf-polynomial-root-factor-conclusion-p
    (interface coefficient-ring polynomial-ring polynomial a)
  (exists (quotient)
    (and
     (bf-polynomial-element-p polynomial-ring quotient)
     (equal
      polynomial
      (bf-polynomial-mul
       polynomial-ring
       quotient
       (bf-polynomial-x-minus
        interface coefficient-ring polynomial-ring a))))))

(defun-sk bf-polynomial-root-factor-statement ()
  (forall
    (interface coefficient-ring polynomial-ring polynomial a)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p polynomial-ring polynomial)
      (bf-polynomial-element-p coefficient-ring a)
      (bf-polynomial-root-p
       interface coefficient-ring polynomial a))
     (bf-polynomial-root-factor-conclusion-p
      interface coefficient-ring polynomial-ring polynomial a))))

(defun-sk bf-polynomial-root-transfer-statement ()
  (forall
    (interface coefficient-ring polynomial-ring p q a b)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p polynomial-ring p)
      (bf-polynomial-element-p polynomial-ring q)
      (bf-polynomial-element-p coefficient-ring a)
      (bf-polynomial-element-p coefficient-ring b)
      (equal
       p
       (bf-polynomial-mul
        polynomial-ring
        q
        (bf-polynomial-x-minus
         interface coefficient-ring polynomial-ring a)))
      (not (equal b a))
      (bf-polynomial-root-p interface coefficient-ring p b))
     (bf-polynomial-root-p
      interface coefficient-ring q b))))

(defun-sk bf-polynomial-roots-le-degree-statement ()
  (forall
    (interface coefficient-ring polynomial-ring polynomial xs)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p polynomial-ring polynomial)
      (bf-polynomial-ring-list-p coefficient-ring xs)
      (bf-polynomial-no-duplicates-p xs)
      (bf-polynomial-all-roots-p
       interface coefficient-ring xs polynomial)
      (not
       (equal
        polynomial
        (bf-polynomial-zero polynomial-ring))))
     (<=
      (len xs)
      (bf-polynomial-degree interface polynomial)))))

(defun-sk bf-polynomial-x-minus-nonzero-statement ()
  (forall (interface coefficient-ring polynomial-ring a)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p coefficient-ring a))
     (not
      (equal
       (bf-polynomial-x-minus
        interface coefficient-ring polynomial-ring a)
       (bf-polynomial-zero polynomial-ring))))))

(defun-sk bf-polynomial-constant-root-zero-statement ()
  (forall
    (interface coefficient-ring polynomial-ring polynomial a)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p polynomial-ring polynomial)
      (bf-polynomial-element-p coefficient-ring a)
      (equal
       (bf-polynomial-degree interface polynomial)
       0)
      (bf-polynomial-root-p
       interface coefficient-ring polynomial a))
     (equal
      polynomial
      (bf-polynomial-zero polynomial-ring)))))

(defun-sk bf-polynomial-root-of-product-statement ()
  (forall (interface coefficient-ring polynomial-ring p q a)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p polynomial-ring p)
      (bf-polynomial-element-p polynomial-ring q)
      (bf-polynomial-element-p coefficient-ring a)
      (bf-polynomial-root-p
       interface
       coefficient-ring
       (bf-polynomial-mul polynomial-ring p q)
       a))
     (or
      (bf-polynomial-root-p interface coefficient-ring p a)
      (bf-polynomial-root-p interface coefficient-ring q a)))))

(defun-sk bf-polynomial-root-scale-constant-statement ()
  (forall (interface coefficient-ring polynomial-ring p c a)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p polynomial-ring p)
      (bf-polynomial-element-p coefficient-ring c)
      (bf-polynomial-element-p coefficient-ring a)
      (not
       (equal c (bf-polynomial-zero coefficient-ring))))
     (iff
      (bf-polynomial-root-p interface coefficient-ring p a)
      (bf-polynomial-root-p
       interface
       coefficient-ring
       (bf-polynomial-mul
        polynomial-ring
        (bf-polynomial-c interface c)
        p)
       a)))))

(defun-sk bf-polynomial-poly-of-roots-nonzero-statement ()
  (forall (interface coefficient-ring polynomial-ring xs)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-ring-list-p coefficient-ring xs))
     (not
      (equal
       (bf-polynomial-poly-of-roots
        interface coefficient-ring polynomial-ring xs)
       (bf-polynomial-zero polynomial-ring))))))

(defun-sk bf-polynomial-deg-poly-of-roots-statement ()
  (forall (interface coefficient-ring polynomial-ring xs)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-ring-list-p coefficient-ring xs))
     (equal
      (bf-polynomial-degree
       interface
       (bf-polynomial-poly-of-roots
        interface coefficient-ring polynomial-ring xs))
      (len xs)))))

(defun-sk bf-polynomial-root-factor-list-conclusion-p
    (interface coefficient-ring polynomial-ring polynomial xs)
  (exists (quotient)
    (and
     (bf-polynomial-element-p polynomial-ring quotient)
     (equal
      polynomial
      (bf-polynomial-mul
       polynomial-ring
       quotient
       (bf-polynomial-poly-of-roots
        interface coefficient-ring polynomial-ring xs))))))

(defun-sk bf-polynomial-root-factor-list-statement ()
  (forall
    (interface coefficient-ring polynomial-ring polynomial xs)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p polynomial-ring polynomial)
      (bf-polynomial-ring-list-p coefficient-ring xs)
      (bf-polynomial-no-duplicates-p xs)
      (bf-polynomial-all-roots-p
       interface coefficient-ring xs polynomial))
     (bf-polynomial-root-factor-list-conclusion-p
      interface
      coefficient-ring
      polynomial-ring
      polynomial
      xs))))

(defun-sk bf-polynomial-degree-factorisation-statement ()
  (forall
    (interface coefficient-ring polynomial-ring polynomial xs quotient)
    (implies
     (and
      (bf-polynomial-context-p
       interface coefficient-ring polynomial-ring)
      (bf-polynomial-element-p polynomial-ring polynomial)
      (bf-polynomial-ring-list-p coefficient-ring xs)
      (bf-polynomial-element-p polynomial-ring quotient)
      (equal
       polynomial
       (bf-polynomial-mul
        polynomial-ring
        quotient
        (bf-polynomial-poly-of-roots
         interface coefficient-ring polynomial-ring xs)))
      (not
       (equal
        quotient
        (bf-polynomial-zero polynomial-ring))))
     (equal
      (bf-polynomial-degree interface polynomial)
      (+
       (bf-polynomial-degree interface quotient)
       (len xs))))))

(defun babel-formal-polynomial-statement ()
  (and
   (bf-polynomial-mynat-add-o-left-statement)
   (bf-polynomial-mynat-add-s-left-statement)
   (bf-polynomial-mynat-zero-le-statement)
   (bf-polynomial-mynat-add-zero-r-statement)
   (bf-polynomial-mynat-succ-le-succ-statement)
   (bf-polynomial-mynat-add-s-r-statement)
   (bf-polynomial-mynat-add-comm-statement)
   (bf-polynomial-sub-eq-zero-l-statement)
   (bf-polynomial-root-factor-statement)
   (bf-polynomial-root-transfer-statement)
   (bf-polynomial-roots-le-degree-statement)
   (bf-polynomial-x-minus-nonzero-statement)
   (bf-polynomial-constant-root-zero-statement)
   (bf-polynomial-root-of-product-statement)
   (bf-polynomial-root-scale-constant-statement)
   (bf-polynomial-poly-of-roots-nonzero-statement)
   (bf-polynomial-deg-poly-of-roots-statement)
   (bf-polynomial-root-factor-list-statement)
   (bf-polynomial-degree-factorisation-statement)))

(value-triple :itpeval-statement-checked)
:q
