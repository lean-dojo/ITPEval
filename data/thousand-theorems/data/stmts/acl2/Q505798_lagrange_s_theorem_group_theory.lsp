;; Statement-only formalization of thousand-theorems corpus artifact Q505798,
;; "Lagrange's theorem (group theory)": for an arbitrary group and subgroup,
;; the subgroup's Nat.card divides the ambient group's Nat.card, with Nat.card
;; equal to zero on infinite carriers. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent an arbitrary group structure and an
;; arbitrary subgroup predicate. All structure laws are explicit below.

(defstub q505798-group-element-p (group element) t)
(defstub q505798-group-mul (group left right) t)
(defstub q505798-group-inv (group element) t)
(defstub q505798-group-one (group) t)
(defstub q505798-subgroup-element-p (group subgroup element) t)

(defun-sk q505798-group-laws-p (group)
  (forall (x y z)
    (and
     (implies
      (q505798-group-element-p group x)
      (and
       (q505798-group-element-p
        group
        (q505798-group-inv group x))
       (equal
        (q505798-group-mul
         group x (q505798-group-one group))
        x)
       (equal
        (q505798-group-mul
         group (q505798-group-one group) x)
        x)
       (equal
        (q505798-group-mul
         group x (q505798-group-inv group x))
        (q505798-group-one group))
       (equal
        (q505798-group-mul
         group (q505798-group-inv group x) x)
        (q505798-group-one group))))
     (implies
      (and
       (q505798-group-element-p group x)
       (q505798-group-element-p group y))
      (q505798-group-element-p
       group
       (q505798-group-mul group x y)))
     (implies
      (and
       (q505798-group-element-p group x)
       (q505798-group-element-p group y)
       (q505798-group-element-p group z))
      (equal
       (q505798-group-mul
        group
        (q505798-group-mul group x y)
        z)
       (q505798-group-mul
        group
        x
        (q505798-group-mul group y z)))))))

(defun q505798-group-p (group)
  (and
   (q505798-group-element-p
    group
    (q505798-group-one group))
   (q505798-group-laws-p group)))

(defun-sk q505798-subgroup-laws-p (group subgroup)
  (forall (x y)
    (and
     (implies
      (q505798-subgroup-element-p group subgroup x)
      (and
       (q505798-group-element-p group x)
       (q505798-subgroup-element-p
        group
        subgroup
        (q505798-group-inv group x))))
     (implies
      (and
       (q505798-subgroup-element-p group subgroup x)
       (q505798-subgroup-element-p group subgroup y))
      (q505798-subgroup-element-p
       group
       subgroup
       (q505798-group-mul group x y))))))

(defun q505798-subgroup-p (group subgroup)
  (and
   (q505798-subgroup-element-p
    group
    subgroup
    (q505798-group-one group))
   (q505798-subgroup-laws-p group subgroup)))

;; Exact duplicate-free enumerations characterize finite carriers. These
;; enumerations remain internal existential witnesses rather than parameters.

(defun-sk q505798-ambient-enumeration-extensional-p
    (group enumeration)
  (forall (x)
    (iff
     (member-equal x enumeration)
     (q505798-group-element-p group x))))

(defun q505798-exact-ambient-enumeration-p
    (group enumeration)
  (and
   (true-listp enumeration)
   (no-duplicatesp-equal enumeration)
   (q505798-ambient-enumeration-extensional-p
    group enumeration)))

(defun-sk q505798-subgroup-enumeration-extensional-p
    (group subgroup enumeration)
  (forall (x)
    (iff
     (member-equal x enumeration)
     (q505798-subgroup-element-p group subgroup x))))

(defun q505798-exact-subgroup-enumeration-p
    (group subgroup enumeration)
  (and
   (true-listp enumeration)
   (no-duplicatesp-equal enumeration)
   (q505798-subgroup-enumeration-extensional-p
    group subgroup enumeration)))

(defun-sk q505798-finite-carrier-p (group)
  (exists (enumeration)
    (q505798-exact-ambient-enumeration-p
     group enumeration)))

(defun q505798-divides-p (divisor dividend)
  (and
   (natp divisor)
   (natp dividend)
   (if (equal divisor 0)
       (equal dividend 0)
     (equal (mod dividend divisor) 0))))

(defun-sk q505798-finite-card-divides-p (group subgroup)
  (exists (ambient-enumeration subgroup-enumeration)
    (and
     (q505798-exact-ambient-enumeration-p
      group ambient-enumeration)
     (q505798-exact-subgroup-enumeration-p
      group subgroup subgroup-enumeration)
     (q505798-divides-p
      (len subgroup-enumeration)
      (len ambient-enumeration)))))

(defun q505798-nat-card-divides-p (group subgroup)
  (or
   ;; An infinite ambient carrier has Nat.card zero, which every natural
   ;; number divides.
   (not (q505798-finite-carrier-p group))
   ;; On finite carriers, exact enumerations recover both Nat.card values.
   (q505798-finite-card-divides-p group subgroup)))

(defun thousand-theorems-q505798-lagranges-theorem-group-theory-statement
    (group subgroup)
  (implies
   (and
    (q505798-group-p group)
    (q505798-subgroup-p group subgroup))
   (q505798-nat-card-divides-p group subgroup)))

(value-triple :itpeval-statement-checked)
:q
