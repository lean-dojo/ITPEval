;; Statement-only formalization of thousand-theorems corpus artifact Q2379132,
;; "Going-up and going-down theorems". It states the two indexed going-up
;; results, the prime-spectrum characterization of going-down, and the
;; localized-spectrum surjectivity criterion. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent arbitrary ring carriers, operations,
;; homomorphisms, and ideal-membership predicates. The structure tags do not
;; enumerate or otherwise restrict any carrier or ideal.

(defstub q2379132-carrier-p (ring value) t)
(defstub q2379132-zero (ring) t)
(defstub q2379132-one (ring) t)
(defstub q2379132-add (ring left right) t)
(defstub q2379132-mul (ring left right) t)
(defstub q2379132-neg (ring value) t)
(defstub q2379132-map (hom value) t)
(defstub q2379132-ideal-member-p (ideal ring value) t)

(defun-sk q2379132-commutative-ring-laws-p (ring)
  (forall (x y z)
    (and
     (implies
      (q2379132-carrier-p ring x)
      (and
       (q2379132-carrier-p ring (q2379132-neg ring x))
       (equal (q2379132-add ring x (q2379132-zero ring)) x)
       (equal (q2379132-add ring (q2379132-zero ring) x) x)
       (equal
        (q2379132-add ring x (q2379132-neg ring x))
        (q2379132-zero ring))
       (equal
        (q2379132-add ring (q2379132-neg ring x) x)
        (q2379132-zero ring))
       (equal (q2379132-mul ring x (q2379132-one ring)) x)
       (equal (q2379132-mul ring (q2379132-one ring) x) x)
       (equal
        (q2379132-mul ring x (q2379132-zero ring))
        (q2379132-zero ring))
       (equal
        (q2379132-mul ring (q2379132-zero ring) x)
        (q2379132-zero ring))))
     (implies
      (and
       (q2379132-carrier-p ring x)
       (q2379132-carrier-p ring y))
      (and
       (q2379132-carrier-p ring (q2379132-add ring x y))
       (q2379132-carrier-p ring (q2379132-mul ring x y))
       (equal
        (q2379132-add ring x y)
        (q2379132-add ring y x))
       (equal
        (q2379132-mul ring x y)
        (q2379132-mul ring y x))))
     (implies
      (and
       (q2379132-carrier-p ring x)
       (q2379132-carrier-p ring y)
       (q2379132-carrier-p ring z))
      (and
       (equal
        (q2379132-add ring (q2379132-add ring x y) z)
        (q2379132-add ring x (q2379132-add ring y z)))
       (equal
        (q2379132-mul ring (q2379132-mul ring x y) z)
        (q2379132-mul ring x (q2379132-mul ring y z)))
       (equal
        (q2379132-mul ring x (q2379132-add ring y z))
        (q2379132-add
         ring
         (q2379132-mul ring x y)
         (q2379132-mul ring x z)))
       (equal
        (q2379132-mul ring (q2379132-add ring x y) z)
        (q2379132-add
         ring
         (q2379132-mul ring x z)
         (q2379132-mul ring y z))))))))

(defun q2379132-commutative-ring-p (ring)
  (and
   (q2379132-carrier-p ring (q2379132-zero ring))
   (q2379132-carrier-p ring (q2379132-one ring))
   (q2379132-commutative-ring-laws-p ring)))

(defun-sk q2379132-no-zero-divisors-p (ring)
  (forall (x y)
    (implies
     (and
      (q2379132-carrier-p ring x)
      (q2379132-carrier-p ring y)
      (equal
       (q2379132-mul ring x y)
       (q2379132-zero ring)))
     (or
      (equal x (q2379132-zero ring))
      (equal y (q2379132-zero ring))))))

(defun q2379132-domain-p (ring)
  (and
   (q2379132-commutative-ring-p ring)
   (not (equal
         (q2379132-zero ring)
         (q2379132-one ring)))
   (q2379132-no-zero-divisors-p ring)))

(defun-sk q2379132-ring-homomorphism-laws-p
    (source target hom)
  (forall (x y)
    (and
     (implies
      (q2379132-carrier-p source x)
      (q2379132-carrier-p
       target
       (q2379132-map hom x)))
     (implies
      (and
       (q2379132-carrier-p source x)
       (q2379132-carrier-p source y))
      (and
       (equal
        (q2379132-map hom (q2379132-add source x y))
        (q2379132-add
         target
         (q2379132-map hom x)
         (q2379132-map hom y)))
       (equal
        (q2379132-map hom (q2379132-mul source x y))
        (q2379132-mul
         target
         (q2379132-map hom x)
         (q2379132-map hom y))))))))

(defun q2379132-ring-homomorphism-p (source target hom)
  (and
   (equal
    (q2379132-map hom (q2379132-zero source))
    (q2379132-zero target))
   (equal
    (q2379132-map hom (q2379132-one source))
    (q2379132-one target))
   (q2379132-ring-homomorphism-laws-p source target hom)))

(defun-sk q2379132-ideal-laws-p (ring ideal)
  (forall (a x y)
    (and
     (implies
      (q2379132-ideal-member-p ideal ring x)
      (and
       (q2379132-carrier-p ring x)
       (q2379132-ideal-member-p
        ideal ring (q2379132-neg ring x))))
     (implies
      (and
       (q2379132-ideal-member-p ideal ring x)
       (q2379132-ideal-member-p ideal ring y))
      (q2379132-ideal-member-p
       ideal ring (q2379132-add ring x y)))
     (implies
      (and
       (q2379132-carrier-p ring a)
       (q2379132-ideal-member-p ideal ring x))
      (q2379132-ideal-member-p
       ideal ring (q2379132-mul ring a x))))))

(defun q2379132-ideal-p (ring ideal)
  (and
   (q2379132-ideal-member-p
    ideal ring (q2379132-zero ring))
   (q2379132-ideal-laws-p ring ideal)))

(defun-sk q2379132-prime-multiplication-law-p (ring ideal)
  (forall (x y)
    (implies
     (and
      (q2379132-carrier-p ring x)
      (q2379132-carrier-p ring y)
      (q2379132-ideal-member-p
       ideal ring (q2379132-mul ring x y)))
     (or
      (q2379132-ideal-member-p ideal ring x)
      (q2379132-ideal-member-p ideal ring y)))))

(defun q2379132-prime-ideal-p (ring ideal)
  (and
   (q2379132-ideal-p ring ideal)
   (not
    (q2379132-ideal-member-p
     ideal ring (q2379132-one ring)))
   (q2379132-prime-multiplication-law-p ring ideal)))

(defun q2379132-coefficients-in-ring-p (ring coefficients)
  (if (consp coefficients)
      (and
       (q2379132-carrier-p ring (car coefficients))
       (q2379132-coefficients-in-ring-p ring (cdr coefficients)))
    (equal coefficients nil)))

(defun q2379132-monic-polynomial-p (ring coefficients)
  (and
   (consp coefficients)
   (q2379132-coefficients-in-ring-p ring coefficients)
   (equal
    (car (last coefficients))
    (q2379132-one ring))))

(defun q2379132-polynomial-eval
    (target hom coefficients x)
  (if (endp coefficients)
      (q2379132-zero target)
    (q2379132-add
     target
     (q2379132-map hom (car coefficients))
     (q2379132-mul
      target
      x
      (q2379132-polynomial-eval
       target hom (cdr coefficients) x)))))

(defun-sk q2379132-integral-element-p
    (source target hom x)
  (exists (coefficients)
    (and
     (q2379132-monic-polynomial-p source coefficients)
     (equal
      (q2379132-polynomial-eval
       target hom coefficients x)
      (q2379132-zero target)))))

(defun-sk q2379132-integral-homomorphism-p
    (source target hom)
  (forall (x)
    (implies
     (q2379132-carrier-p target x)
     (q2379132-integral-element-p
      source target hom x))))

(defun-sk q2379132-kernel-contained-in-ideal-p
    (source target hom ideal)
  (forall (x)
    (implies
     (and
      (q2379132-carrier-p source x)
      (equal
       (q2379132-map hom x)
       (q2379132-zero target)))
     (q2379132-ideal-member-p ideal source x))))

(defun-sk q2379132-contraction-equals-p
    (source target hom upstairs downstairs)
  (forall (x)
    (implies
     (q2379132-carrier-p source x)
     (equal
      (if
          (q2379132-ideal-member-p
           upstairs target (q2379132-map hom x))
          t
        nil)
      (if
          (q2379132-ideal-member-p downstairs source x)
          t
        nil)))))

(defun-sk q2379132-prime-over-p
    (source target hom downstairs)
  (exists (upstairs)
    (and
     (q2379132-prime-ideal-p target upstairs)
     (q2379132-contraction-equals-p
      source target hom upstairs downstairs))))

(defun-sk q2379132-ideal-contained-p
    (ring smaller larger)
  (forall (x)
    (implies
     (and
      (q2379132-carrier-p ring x)
      (q2379132-ideal-member-p smaller ring x))
     (q2379132-ideal-member-p larger ring x))))

(defun-sk q2379132-contraction-contained-in-ideal-p
    (source target hom upstairs downstairs)
  (forall (x)
    (implies
     (and
      (q2379132-carrier-p source x)
      (q2379132-ideal-member-p
       upstairs target (q2379132-map hom x)))
     (q2379132-ideal-member-p downstairs source x))))

(defun-sk q2379132-ideal-below-contraction-p
    (source target hom downstairs upstairs)
  (forall (x)
    (implies
     (and
      (q2379132-carrier-p source x)
      (q2379132-ideal-member-p downstairs source x))
     (q2379132-ideal-member-p
      upstairs target (q2379132-map hom x)))))

(defun-sk q2379132-prime-above-over-p
    (source target hom downstairs initial)
  (exists (upstairs)
    (and
     (q2379132-prime-ideal-p target upstairs)
     (q2379132-ideal-contained-p target initial upstairs)
     (q2379132-contraction-equals-p
      source target hom upstairs downstairs))))

(defun-sk q2379132-prime-below-over-p
    (source target hom downstairs upper)
  (exists (lower)
    (and
     (q2379132-prime-ideal-p target lower)
     (q2379132-ideal-contained-p target lower upper)
     (q2379132-contraction-equals-p
      source target hom lower downstairs))))

(defun-sk q2379132-has-going-down-p
    (source target hom)
  (forall (p q upper)
    (implies
     (and
      (q2379132-prime-ideal-p source p)
      (q2379132-prime-ideal-p source q)
      (q2379132-ideal-contained-p source p q)
      (q2379132-prime-ideal-p target upper)
      (q2379132-contraction-equals-p
       source target hom upper q))
     (q2379132-prime-below-over-p
      source target hom p upper))))

(defun-sk q2379132-generalizing-prime-spectrum-comap-p
    (source target hom)
  (forall (upper p)
    (implies
     (and
      (q2379132-prime-ideal-p target upper)
      (q2379132-prime-ideal-p source p)
      (q2379132-ideal-below-contraction-p
       source target hom p upper))
     (q2379132-prime-below-over-p
      source target hom p upper))))

(defun-sk q2379132-local-prime-spectrum-comap-surjective-p
    (source target hom upper)
  (forall (p)
    (implies
     (and
      (q2379132-prime-ideal-p source p)
      (q2379132-ideal-below-contraction-p
       source target hom p upper))
     (q2379132-prime-below-over-p
      source target hom p upper))))

(defun-sk q2379132-all-local-prime-spectrum-comaps-surjective-p
    (source target hom)
  (forall (upper)
    (implies
     (q2379132-prime-ideal-p target upper)
     (q2379132-local-prime-spectrum-comap-surjective-p
      source target hom upper))))

(defun-sk
    thousand-theorems-q2379132-going-up-and-going-down-theorems-statement
    ()
  (forall (source target hom prime)
    (implies
     (and
      (q2379132-commutative-ring-p source)
      (q2379132-domain-p target)
      (q2379132-ring-homomorphism-p source target hom)
      (q2379132-integral-homomorphism-p source target hom)
      (q2379132-prime-ideal-p source prime)
      (q2379132-kernel-contained-in-ideal-p
       source target hom prime))
     (q2379132-prime-over-p
      source target hom prime))))

(defun-sk
    q2379132-exists-ideal-over-prime-of-integral-of-prime-statement
    ()
  (forall (source target hom prime initial)
    (implies
     (and
      (q2379132-commutative-ring-p source)
      (q2379132-commutative-ring-p target)
      (q2379132-ring-homomorphism-p source target hom)
      (q2379132-integral-homomorphism-p source target hom)
      (q2379132-prime-ideal-p source prime)
      (q2379132-prime-ideal-p target initial)
      (q2379132-contraction-contained-in-ideal-p
       source target hom initial prime))
     (q2379132-prime-above-over-p
      source target hom prime initial))))

(defun-sk
    q2379132-has-going-down-iff-generalizing-comap-statement
    ()
  (forall (source target hom)
    (implies
     (and
      (q2379132-commutative-ring-p source)
      (q2379132-commutative-ring-p target)
      (q2379132-ring-homomorphism-p source target hom))
     (iff
      (q2379132-has-going-down-p source target hom)
      (q2379132-generalizing-prime-spectrum-comap-p
       source target hom)))))

(defun-sk
    q2379132-has-going-down-of-local-surjectivity-statement
    ()
  (forall (source target hom)
    (implies
     (and
      (q2379132-commutative-ring-p source)
      (q2379132-commutative-ring-p target)
      (q2379132-ring-homomorphism-p source target hom)
      (q2379132-all-local-prime-spectrum-comaps-surjective-p
       source target hom))
     (q2379132-has-going-down-p source target hom))))

(value-triple :itpeval-statement-checked)
:q
