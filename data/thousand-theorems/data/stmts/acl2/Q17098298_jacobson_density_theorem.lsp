;; Statement-only formalization of thousand-theorems corpus artifact Q17098298,
;; "Jacobson density theorem": an endomorphism-linear self-map of an arbitrary
;; semisimple module agrees on every finite subset with scalar action by some
;; element of the original ring. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent arbitrary rings, modules,
;; submodules, and maps. Structure tags do not enumerate or bound carriers;
;; every algebraic law and every quantified condition used by the statement
;; is explicit below.

(defstub q17098298-ring-member-p (ring value) t)
(defstub q17098298-ring-zero (ring) t)
(defstub q17098298-ring-one (ring) t)
(defstub q17098298-ring-add (ring left right) t)
(defstub q17098298-ring-multiply (ring left right) t)
(defstub q17098298-ring-negate (ring value) t)

(defstub q17098298-module-member-p (ring module value) t)
(defstub q17098298-module-zero (ring module) t)
(defstub q17098298-module-add (ring module left right) t)
(defstub q17098298-module-negate (ring module value) t)
(defstub q17098298-module-smul (ring module scalar value) t)

(defstub q17098298-submodule-member-p
  (ring module submodule value)
  t)

(defstub q17098298-linear-map-apply
  (ring module linear-map value)
  t)

;; Rings in the source need not be nontrivial.

(defun-sk q17098298-ring-laws-p (ring)
  (forall (x y z)
    (and
     (implies
      (and
       (q17098298-ring-member-p ring x)
       (q17098298-ring-member-p ring y))
      (and
       (q17098298-ring-member-p
        ring (q17098298-ring-add ring x y))
       (q17098298-ring-member-p
        ring (q17098298-ring-multiply ring x y))
       (equal
        (q17098298-ring-add ring x y)
        (q17098298-ring-add ring y x))))
     (implies
      (q17098298-ring-member-p ring x)
      (and
       (q17098298-ring-member-p
        ring (q17098298-ring-negate ring x))
       (equal
        (q17098298-ring-add
         ring x (q17098298-ring-zero ring))
        x)
       (equal
        (q17098298-ring-add
         ring x (q17098298-ring-negate ring x))
        (q17098298-ring-zero ring))
       (equal
        (q17098298-ring-multiply
         ring x (q17098298-ring-one ring))
        x)
       (equal
        (q17098298-ring-multiply
         ring (q17098298-ring-one ring) x)
        x)))
     (implies
      (and
       (q17098298-ring-member-p ring x)
       (q17098298-ring-member-p ring y)
       (q17098298-ring-member-p ring z))
      (and
       (equal
        (q17098298-ring-add
         ring (q17098298-ring-add ring x y) z)
        (q17098298-ring-add
         ring x (q17098298-ring-add ring y z)))
       (equal
        (q17098298-ring-multiply
         ring (q17098298-ring-multiply ring x y) z)
        (q17098298-ring-multiply
         ring x (q17098298-ring-multiply ring y z)))
       (equal
        (q17098298-ring-multiply
         ring x (q17098298-ring-add ring y z))
        (q17098298-ring-add
         ring
         (q17098298-ring-multiply ring x y)
         (q17098298-ring-multiply ring x z)))
       (equal
        (q17098298-ring-multiply
         ring (q17098298-ring-add ring x y) z)
        (q17098298-ring-add
         ring
         (q17098298-ring-multiply ring x z)
         (q17098298-ring-multiply ring y z))))))))

(defun q17098298-ring-p (ring)
  (and
   (q17098298-ring-member-p
    ring (q17098298-ring-zero ring))
   (q17098298-ring-member-p
    ring (q17098298-ring-one ring))
   (q17098298-ring-laws-p ring)))

;; Additive commutative groups with a left action of the arbitrary ring.

(defun-sk q17098298-module-laws-p (ring module)
  (forall (a b u v w)
    (and
     (implies
      (and
       (q17098298-module-member-p ring module u)
       (q17098298-module-member-p ring module v))
      (and
       (q17098298-module-member-p
        ring module
        (q17098298-module-add ring module u v))
       (equal
        (q17098298-module-add ring module u v)
        (q17098298-module-add ring module v u))))
     (implies
      (q17098298-module-member-p ring module u)
      (and
       (q17098298-module-member-p
        ring module
        (q17098298-module-negate ring module u))
       (equal
        (q17098298-module-add
         ring module u (q17098298-module-zero ring module))
        u)
       (equal
        (q17098298-module-add
         ring module u
         (q17098298-module-negate ring module u))
        (q17098298-module-zero ring module))
       (equal
        (q17098298-module-smul
         ring module (q17098298-ring-one ring) u)
        u)
       (equal
        (q17098298-module-smul
         ring module (q17098298-ring-zero ring) u)
        (q17098298-module-zero ring module))))
     (implies
      (and
       (q17098298-module-member-p ring module u)
       (q17098298-module-member-p ring module v)
       (q17098298-module-member-p ring module w))
      (equal
       (q17098298-module-add
        ring module
        (q17098298-module-add ring module u v)
        w)
       (q17098298-module-add
        ring module u
        (q17098298-module-add ring module v w))))
     (implies
      (and
       (q17098298-ring-member-p ring a)
       (q17098298-module-member-p ring module u))
      (q17098298-module-member-p
       ring module
       (q17098298-module-smul ring module a u)))
     (implies
      (q17098298-ring-member-p ring a)
      (equal
       (q17098298-module-smul
        ring module a (q17098298-module-zero ring module))
       (q17098298-module-zero ring module)))
     (implies
      (and
       (q17098298-ring-member-p ring a)
       (q17098298-module-member-p ring module u)
       (q17098298-module-member-p ring module v))
      (equal
       (q17098298-module-smul
        ring module a
        (q17098298-module-add ring module u v))
       (q17098298-module-add
        ring module
        (q17098298-module-smul ring module a u)
        (q17098298-module-smul ring module a v))))
     (implies
      (and
       (q17098298-ring-member-p ring a)
       (q17098298-ring-member-p ring b)
       (q17098298-module-member-p ring module u))
      (and
       (equal
        (q17098298-module-smul
         ring module (q17098298-ring-add ring a b) u)
        (q17098298-module-add
         ring module
         (q17098298-module-smul ring module a u)
         (q17098298-module-smul ring module b u)))
       (equal
        (q17098298-module-smul
         ring module (q17098298-ring-multiply ring a b) u)
        (q17098298-module-smul
         ring module a
         (q17098298-module-smul ring module b u))))))))

(defun q17098298-module-p (ring module)
  (and
   (q17098298-ring-p ring)
   (q17098298-module-member-p
    ring module (q17098298-module-zero ring module))
   (q17098298-module-laws-p ring module)))

;; Submodules are arbitrary predicates satisfying the full closure laws.

(defun-sk q17098298-submodule-laws-p
    (ring module submodule)
  (forall (a x y)
    (and
     (implies
      (q17098298-submodule-member-p
       ring module submodule x)
      (q17098298-module-member-p ring module x))
     (implies
      (and
       (q17098298-submodule-member-p
        ring module submodule x)
       (q17098298-submodule-member-p
        ring module submodule y))
      (q17098298-submodule-member-p
       ring module submodule
       (q17098298-module-add ring module x y)))
     (implies
      (q17098298-submodule-member-p
       ring module submodule x)
      (q17098298-submodule-member-p
       ring module submodule
       (q17098298-module-negate ring module x)))
     (implies
      (and
       (q17098298-ring-member-p ring a)
       (q17098298-submodule-member-p
        ring module submodule x))
      (q17098298-submodule-member-p
       ring module submodule
       (q17098298-module-smul ring module a x))))))

(defun q17098298-submodule-p (ring module submodule)
  (and
   (q17098298-submodule-member-p
    ring module submodule
    (q17098298-module-zero ring module))
   (q17098298-submodule-laws-p ring module submodule)))

;; A complement has zero intersection with the given submodule and every
;; module element is a sum of one element from each submodule.

(defun-sk q17098298-decomposition-exists-p
    (ring module left-submodule right-submodule value)
  (exists (left-value right-value)
    (and
     (q17098298-submodule-member-p
      ring module left-submodule left-value)
     (q17098298-submodule-member-p
      ring module right-submodule right-value)
     (equal
      value
      (q17098298-module-add
       ring module left-value right-value)))))

(defun-sk q17098298-complement-laws-p
    (ring module left-submodule right-submodule)
  (forall (value)
    (and
     (implies
      (and
       (q17098298-submodule-member-p
        ring module left-submodule value)
       (q17098298-submodule-member-p
        ring module right-submodule value))
      (equal value (q17098298-module-zero ring module)))
     (implies
      (q17098298-module-member-p ring module value)
      (q17098298-decomposition-exists-p
       ring module left-submodule right-submodule value)))))

(defun q17098298-complement-p
    (ring module left-submodule right-submodule)
  (and
   (q17098298-submodule-p
    ring module right-submodule)
   (q17098298-complement-laws-p
    ring module left-submodule right-submodule)))

(defun-sk q17098298-complement-exists-p
    (ring module submodule)
  (exists (complement)
    (q17098298-complement-p
     ring module submodule complement)))

(defun-sk q17098298-semisimple-laws-p (ring module)
  (forall (submodule)
    (implies
     (q17098298-submodule-p ring module submodule)
     (q17098298-complement-exists-p
      ring module submodule))))

(defun q17098298-semisimple-module-p (ring module)
  (and
   (q17098298-module-p ring module)
   (q17098298-semisimple-laws-p ring module)))

;; The endomorphism ring consists of all R-linear self-maps of the module.

(defun-sk q17098298-endomorphism-laws-p
    (ring module endomorphism)
  (forall (a x y)
    (and
     (implies
      (q17098298-module-member-p ring module x)
      (q17098298-module-member-p
       ring module
       (q17098298-linear-map-apply
        ring module endomorphism x)))
     (implies
      (and
       (q17098298-module-member-p ring module x)
       (q17098298-module-member-p ring module y))
      (equal
       (q17098298-linear-map-apply
        ring module endomorphism
        (q17098298-module-add ring module x y))
       (q17098298-module-add
        ring module
        (q17098298-linear-map-apply
         ring module endomorphism x)
        (q17098298-linear-map-apply
         ring module endomorphism y))))
     (implies
      (and
       (q17098298-ring-member-p ring a)
       (q17098298-module-member-p ring module x))
      (equal
       (q17098298-linear-map-apply
        ring module endomorphism
        (q17098298-module-smul ring module a x))
       (q17098298-module-smul
        ring module a
        (q17098298-linear-map-apply
         ring module endomorphism x)))))))

(defun q17098298-endomorphism-p
    (ring module endomorphism)
  (q17098298-endomorphism-laws-p
   ring module endomorphism))

;; A member of End(End_R(M), M) is additive and commutes with every R-linear
;; endomorphism under the evaluation action.

(defun-sk q17098298-endomorphism-linear-laws-p
    (ring module linear-map)
  (forall (endomorphism x y)
    (and
     (implies
      (q17098298-module-member-p ring module x)
      (q17098298-module-member-p
       ring module
       (q17098298-linear-map-apply
        ring module linear-map x)))
     (implies
      (and
       (q17098298-module-member-p ring module x)
       (q17098298-module-member-p ring module y))
      (equal
       (q17098298-linear-map-apply
        ring module linear-map
        (q17098298-module-add ring module x y))
       (q17098298-module-add
        ring module
        (q17098298-linear-map-apply
         ring module linear-map x)
        (q17098298-linear-map-apply
         ring module linear-map y))))
     (implies
      (and
       (q17098298-endomorphism-p
        ring module endomorphism)
       (q17098298-module-member-p ring module x))
      (equal
       (q17098298-linear-map-apply
        ring module linear-map
        (q17098298-linear-map-apply
         ring module endomorphism x))
       (q17098298-linear-map-apply
        ring module endomorphism
        (q17098298-linear-map-apply
         ring module linear-map x)))))))

(defun q17098298-endomorphism-linear-map-p
    (ring module linear-map)
  (q17098298-endomorphism-linear-laws-p
   ring module linear-map))

;; Duplicate-free module-element lists are canonical representatives of the
;; source Finset. Only this source object is finite.

(defun q17098298-module-list-p (ring module values)
  (if (consp values)
      (and
       (q17098298-module-member-p
        ring module (car values))
       (q17098298-module-list-p
        ring module (cdr values)))
    (equal values nil)))

(defun q17098298-finite-subset-p
    (ring module finite-subset)
  (and
   (true-listp finite-subset)
   (no-duplicatesp-equal finite-subset)
   (q17098298-module-list-p
    ring module finite-subset)))

;; The scalar witness remains existentially quantified inside the conclusion.

(defun-sk q17098298-scalar-agreement-p
    (ring module linear-map finite-subset scalar)
  (forall (value)
    (implies
     (member-equal value finite-subset)
     (equal
      (q17098298-linear-map-apply
       ring module linear-map value)
      (q17098298-module-smul
       ring module scalar value)))))

(defun-sk q17098298-scalar-agrees-on-finite-subset-p
    (ring module linear-map finite-subset)
  (exists (scalar)
    (and
     (q17098298-ring-member-p ring scalar)
     (q17098298-scalar-agreement-p
      ring module linear-map finite-subset scalar))))

(defun-sk
    thousand-theorems-q17098298-jacobson-density-theorem-statement
    ()
  (forall (ring module linear-map finite-subset)
    (implies
     (and
      (q17098298-semisimple-module-p ring module)
      (q17098298-endomorphism-linear-map-p
       ring module linear-map)
      (q17098298-finite-subset-p
       ring module finite-subset))
     (q17098298-scalar-agrees-on-finite-subset-p
      ring module linear-map finite-subset))))

(value-triple :itpeval-statement-checked)
:q
