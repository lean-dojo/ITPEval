;; Statement-only formalization of thousand-theorems corpus artifact Q2226800,
;; "Schur-Zassenhaus theorem": a normal subgroup of an arbitrary group whose
;; cardinality is coprime to its index has a left complement. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic interfaces represent an arbitrary group and arbitrary
;; subgroup predicates. Every group, subgroup, normality, cardinality, and
;; complement law used by the statement is explicit below.

(defstub q2226800-carrier-member-p (group element) t)
(defstub q2226800-multiply (group left right) t)
(defstub q2226800-invert (group element) t)
(defstub q2226800-identity (group) t)
(defstub q2226800-subgroup-member-p (subgroup element) t)

(defun-sk q2226800-group-laws-p (group)
  (forall (x y z)
    (and
     (implies
      (q2226800-carrier-member-p group x)
      (and
       (q2226800-carrier-member-p
        group
        (q2226800-invert group x))
       (equal
        (q2226800-multiply
         group
         (q2226800-identity group)
         x)
        x)
       (equal
        (q2226800-multiply
         group
         x
         (q2226800-identity group))
        x)
       (equal
        (q2226800-multiply
         group
         (q2226800-invert group x)
         x)
        (q2226800-identity group))
       (equal
        (q2226800-multiply
         group
         x
         (q2226800-invert group x))
        (q2226800-identity group))))
     (implies
      (and
       (q2226800-carrier-member-p group x)
       (q2226800-carrier-member-p group y))
      (q2226800-carrier-member-p
       group
       (q2226800-multiply group x y)))
     (implies
      (and
       (q2226800-carrier-member-p group x)
       (q2226800-carrier-member-p group y)
       (q2226800-carrier-member-p group z))
      (equal
       (q2226800-multiply
        group
        (q2226800-multiply group x y)
        z)
       (q2226800-multiply
        group
        x
        (q2226800-multiply group y z)))))))

(defun q2226800-group-p (group)
  (and
   (q2226800-carrier-member-p
    group
    (q2226800-identity group))
   (q2226800-group-laws-p group)))

(defun-sk q2226800-subgroup-laws-p (group subgroup)
  (forall (x y)
    (and
     (implies
      (q2226800-subgroup-member-p subgroup x)
      (and
       (q2226800-carrier-member-p group x)
       (q2226800-subgroup-member-p
        subgroup
        (q2226800-invert group x))))
     (implies
      (and
       (q2226800-subgroup-member-p subgroup x)
       (q2226800-subgroup-member-p subgroup y))
      (q2226800-subgroup-member-p
       subgroup
       (q2226800-multiply group x y))))))

(defun q2226800-subgroup-p (group subgroup)
  (and
   (q2226800-group-p group)
   (q2226800-subgroup-member-p
    subgroup
    (q2226800-identity group))
   (q2226800-subgroup-laws-p group subgroup)))

(defun-sk q2226800-normal-p (group subgroup)
  (forall (group-element subgroup-element)
    (implies
     (and
      (q2226800-carrier-member-p group group-element)
      (q2226800-subgroup-member-p subgroup subgroup-element))
     (q2226800-subgroup-member-p
      subgroup
      (q2226800-multiply
       group
       (q2226800-multiply
        group
        group-element
        subgroup-element)
       (q2226800-invert group group-element))))))

;; For a subgroup, coprimality of Nat.card N and the index has exactly three
;; forms. N may be the whole group (index one), N may be trivial (cardinality
;; one), or both N and the ambient group are finite. Exact duplicate-free
;; enumerations express the finite case without restricting the arbitrary
;; carrier in the other two cases.

(defun-sk q2226800-whole-subgroup-p (group subgroup)
  (forall (element)
    (iff
     (q2226800-subgroup-member-p subgroup element)
     (q2226800-carrier-member-p group element))))

(defun-sk q2226800-trivial-subgroup-p (group subgroup)
  (forall (element)
    (iff
     (q2226800-subgroup-member-p subgroup element)
     (equal element (q2226800-identity group)))))

(defun-sk q2226800-exact-carrier-enumeration-p
    (group elements)
  (forall (element)
    (iff
     (if (member-equal element elements) t nil)
     (q2226800-carrier-member-p group element))))

(defun-sk q2226800-exact-subgroup-enumeration-p
    (subgroup elements)
  (forall (element)
    (iff
     (if (member-equal element elements) t nil)
     (q2226800-subgroup-member-p subgroup element))))

(defun q2226800-finite-carrier-certificate-p
    (group elements)
  (and
   (true-listp elements)
   (no-duplicatesp-equal elements)
   (q2226800-exact-carrier-enumeration-p
    group elements)))

(defun q2226800-finite-subgroup-certificate-p
    (subgroup elements)
  (and
   (true-listp elements)
   (no-duplicatesp-equal elements)
   (q2226800-exact-subgroup-enumeration-p
    subgroup elements)))

(defun q2226800-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond
       ((equal a 0) b)
       ((equal b 0) a)
       ((< a b)
        (q2226800-gcd a (- b a)))
       (t
        (q2226800-gcd (- a b) b)))
    0))

(defun-sk q2226800-finite-coprime-card-index-p
    (group subgroup)
  (exists (carrier-elements subgroup-elements index)
    (and
     (q2226800-finite-carrier-certificate-p
      group carrier-elements)
     (q2226800-finite-subgroup-certificate-p
      subgroup subgroup-elements)
     (natp index)
     (< 0 index)
     (equal
      (len carrier-elements)
      (* (len subgroup-elements) index))
     (equal
      (q2226800-gcd
       (len subgroup-elements)
       index)
      1))))

(defun q2226800-coprime-card-index-p
    (group subgroup)
  (or
   (q2226800-whole-subgroup-p group subgroup)
   (q2226800-trivial-subgroup-p group subgroup)
   (q2226800-finite-coprime-card-index-p
    group subgroup)))

;; IsComplement' H N says that multiplication H x N -> G is bijective. Under
;; the coprimality cases above, a complement can be represented faithfully as
;; the carrier itself when N is trivial, or by an internally quantified finite
;; enumeration when G is finite or N is the whole group.

(defun q2226800-list-member-p (elements element)
  (if (member-equal element elements) t nil))

(defun-sk q2226800-list-subgroup-laws-p
    (group elements)
  (forall (x y)
    (and
     (implies
      (q2226800-list-member-p elements x)
      (and
       (q2226800-carrier-member-p group x)
       (q2226800-list-member-p
        elements
        (q2226800-invert group x))))
     (implies
      (and
       (q2226800-list-member-p elements x)
       (q2226800-list-member-p elements y))
      (q2226800-list-member-p
       elements
       (q2226800-multiply group x y))))))

(defun q2226800-list-subgroup-p
    (group elements)
  (and
   (q2226800-group-p group)
   (true-listp elements)
   (no-duplicatesp-equal elements)
   (q2226800-list-member-p
    elements
    (q2226800-identity group))
   (q2226800-list-subgroup-laws-p
    group elements)))

(defun-sk q2226800-list-factorization-exists-p
    (group subgroup complement-elements element)
  (exists (complement-element subgroup-element)
    (and
     (q2226800-list-member-p
      complement-elements complement-element)
     (q2226800-subgroup-member-p
      subgroup subgroup-element)
     (equal
      (q2226800-multiply
       group complement-element subgroup-element)
      element))))

(defun-sk q2226800-list-product-map-surjective-p
    (group subgroup complement-elements)
  (forall (element)
    (implies
     (q2226800-carrier-member-p group element)
     (q2226800-list-factorization-exists-p
      group subgroup complement-elements element))))

(defun-sk q2226800-list-product-map-injective-p
    (group subgroup complement-elements)
  (forall
   (left-complement-element left-subgroup-element
    right-complement-element right-subgroup-element)
   (implies
    (and
     (q2226800-list-member-p
      complement-elements left-complement-element)
     (q2226800-subgroup-member-p
      subgroup left-subgroup-element)
     (q2226800-list-member-p
      complement-elements right-complement-element)
     (q2226800-subgroup-member-p
      subgroup right-subgroup-element)
     (equal
      (q2226800-multiply
       group
       left-complement-element
       left-subgroup-element)
      (q2226800-multiply
       group
       right-complement-element
       right-subgroup-element)))
    (and
     (equal
      left-complement-element
      right-complement-element)
     (equal
      left-subgroup-element
      right-subgroup-element)))))

(defun q2226800-list-left-complement-p
    (group subgroup complement-elements)
  (and
   (q2226800-list-subgroup-p
    group complement-elements)
   (q2226800-list-product-map-surjective-p
    group subgroup complement-elements)
   (q2226800-list-product-map-injective-p
    group subgroup complement-elements)))

(defun-sk q2226800-list-left-complement-exists-p
    (group subgroup)
  (exists (complement-elements)
    (q2226800-list-left-complement-p
     group subgroup complement-elements)))

(defun-sk q2226800-carrier-factorization-exists-p
    (group subgroup element)
  (exists (complement-element subgroup-element)
    (and
     (q2226800-carrier-member-p
      group complement-element)
     (q2226800-subgroup-member-p
      subgroup subgroup-element)
     (equal
      (q2226800-multiply
       group complement-element subgroup-element)
      element))))

(defun-sk q2226800-carrier-product-map-surjective-p
    (group subgroup)
  (forall (element)
    (implies
     (q2226800-carrier-member-p group element)
     (q2226800-carrier-factorization-exists-p
      group subgroup element))))

(defun-sk q2226800-carrier-product-map-injective-p
    (group subgroup)
  (forall
   (left-complement-element left-subgroup-element
    right-complement-element right-subgroup-element)
   (implies
    (and
     (q2226800-carrier-member-p
      group left-complement-element)
     (q2226800-subgroup-member-p
      subgroup left-subgroup-element)
     (q2226800-carrier-member-p
      group right-complement-element)
     (q2226800-subgroup-member-p
      subgroup right-subgroup-element)
     (equal
      (q2226800-multiply
       group
       left-complement-element
       left-subgroup-element)
      (q2226800-multiply
       group
       right-complement-element
       right-subgroup-element)))
    (and
     (equal
      left-complement-element
      right-complement-element)
     (equal
      left-subgroup-element
      right-subgroup-element)))))

(defun q2226800-carrier-left-complement-p
    (group subgroup)
  (and
   (q2226800-group-p group)
   (q2226800-carrier-product-map-surjective-p
    group subgroup)
   (q2226800-carrier-product-map-injective-p
    group subgroup)))

(defun q2226800-left-complement-exists-p
    (group subgroup)
  (or
   (q2226800-carrier-left-complement-p
    group subgroup)
   (q2226800-list-left-complement-exists-p
    group subgroup)))

(defun-sk thousand-theorems-q2226800-schur-zassenhaus-theorem-statement
    ()
  (forall (group subgroup)
    (implies
     (and
      (q2226800-subgroup-p group subgroup)
      (q2226800-normal-p group subgroup)
      (q2226800-coprime-card-index-p
       group subgroup))
     (q2226800-left-complement-exists-p
      group subgroup))))

(value-triple :itpeval-statement-checked)
:q
