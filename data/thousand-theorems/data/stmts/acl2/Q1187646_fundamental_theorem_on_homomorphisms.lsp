;; Statement-only formalization of thousand-theorems corpus artifact Q1187646,
;; "Fundamental theorem on homomorphisms": for every group homomorphism, the
;; canonical map from the quotient by its kernel to its range is a group
;; isomorphism. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative generic symbols represent arbitrary group carriers,
;; operations, and homomorphisms. Group identifiers only index the structures;
;; they do not enumerate or otherwise restrict their potentially infinite
;; carriers. Every required law is explicit below.

(defstub q1187646-element-p (group element) t)
(defstub q1187646-identity (group) t)
(defstub q1187646-multiply (group left right) t)
(defstub q1187646-inverse (group element) t)
(defstub q1187646-hom (source target element) t)

(defun-sk q1187646-group-laws-p (group)
  (forall (x y z)
    (and
     (implies
      (q1187646-element-p group x)
      (and
       (q1187646-element-p
        group
        (q1187646-inverse group x))
       (equal
        (q1187646-multiply
         group
         (q1187646-identity group)
         x)
        x)
       (equal
        (q1187646-multiply
         group
         x
         (q1187646-identity group))
        x)
       (equal
        (q1187646-multiply
         group
         (q1187646-inverse group x)
         x)
        (q1187646-identity group))
       (equal
        (q1187646-multiply
         group
         x
         (q1187646-inverse group x))
        (q1187646-identity group))))
     (implies
      (and
       (q1187646-element-p group x)
       (q1187646-element-p group y))
      (q1187646-element-p
       group
       (q1187646-multiply group x y)))
     (implies
      (and
       (q1187646-element-p group x)
       (q1187646-element-p group y)
       (q1187646-element-p group z))
      (equal
       (q1187646-multiply
        group
        (q1187646-multiply group x y)
        z)
       (q1187646-multiply
        group
        x
        (q1187646-multiply group y z)))))))

(defun q1187646-group-p (group)
  (and
   (q1187646-element-p
    group
    (q1187646-identity group))
   (q1187646-group-laws-p group)))

(defun-sk q1187646-hom-laws-p (source target)
  (forall (x y)
    (and
     (implies
      (q1187646-element-p source x)
      (q1187646-element-p
       target
       (q1187646-hom source target x)))
     (implies
      (and
       (q1187646-element-p source x)
       (q1187646-element-p source y))
      (equal
       (q1187646-hom
        source
        target
        (q1187646-multiply source x y))
       (q1187646-multiply
        target
        (q1187646-hom source target x)
        (q1187646-hom source target y)))))))

(defun q1187646-hom-p (source target)
  (and
   (equal
    (q1187646-hom
     source
     target
     (q1187646-identity source))
    (q1187646-identity target))
   (q1187646-hom-laws-p source target)))

;; The range is the exact image of the source carrier, with its group
;; structure inherited from the target.

(defun-sk q1187646-range-member-p (source target value)
  (exists (preimage)
    (and
     (q1187646-element-p source preimage)
     (equal
      (q1187646-hom source target preimage)
      value))))

(defun-sk q1187646-range-subgroup-laws-p (source target)
  (forall (x y)
    (and
     (implies
      (q1187646-range-member-p source target x)
      (and
       (q1187646-element-p target x)
       (q1187646-range-member-p
        source
        target
        (q1187646-inverse target x))))
     (implies
      (and
       (q1187646-range-member-p source target x)
       (q1187646-range-member-p source target y))
      (q1187646-range-member-p
       source
       target
       (q1187646-multiply target x y))))))

(defun q1187646-range-subgroup-p (source target)
  (and
   (q1187646-range-member-p
    source
    target
    (q1187646-identity target))
   (q1187646-range-subgroup-laws-p source target)))

;; Representatives x and y define the same element of G/ker(phi) exactly
;; when x^-1*y lies in the kernel.

(defun q1187646-kernel-quotient-equivalent-p
    (source target x y)
  (and
   (q1187646-element-p source x)
   (q1187646-element-p source y)
   (equal
    (q1187646-hom
     source
     target
     (q1187646-multiply
      source
      (q1187646-inverse source x)
      y))
    (q1187646-identity target))))

;; The canonical map is [x] |-> phi(x). Equality of its values is equivalent
;; to the kernel quotient relation (well-definedness and injectivity), it
;; preserves multiplication, and every element of the range has a
;; representative (surjectivity).

(defun-sk q1187646-canonical-map-laws-p (source target)
  (forall (x y)
    (and
     (implies
      (q1187646-element-p source x)
      (q1187646-range-member-p
       source
       target
       (q1187646-hom source target x)))
     (implies
      (and
       (q1187646-element-p source x)
       (q1187646-element-p source y))
      (and
       (iff
        (q1187646-kernel-quotient-equivalent-p
         source target x y)
        (equal
         (q1187646-hom source target x)
         (q1187646-hom source target y)))
       (equal
        (q1187646-hom
         source
         target
         (q1187646-multiply source x y))
        (q1187646-multiply
         target
         (q1187646-hom source target x)
         (q1187646-hom source target y))))))))

(defun-sk q1187646-canonical-preimage-exists-p
    (source target value)
  (exists (representative)
    (and
     (q1187646-element-p source representative)
     (equal
      (q1187646-hom source target representative)
      value))))

(defun-sk q1187646-canonical-map-surjective-p (source target)
  (forall (value)
    (implies
     (q1187646-range-member-p source target value)
     (q1187646-canonical-preimage-exists-p
      source target value))))

(defun q1187646-canonical-quotient-range-isomorphism-p
    (source target)
  (and
   (q1187646-range-subgroup-p source target)
   (q1187646-canonical-map-laws-p source target)
   (q1187646-canonical-map-surjective-p source target)))

(defun-sk
    thousand-theorems-q1187646-quotient-ker-equiv-range-statement
    ()
  (forall (source target)
    (implies
     (and
      (q1187646-group-p source)
      (q1187646-group-p target)
      (q1187646-hom-p source target))
     (q1187646-canonical-quotient-range-isomorphism-p
      source target))))

(value-triple :itpeval-statement-checked)
:q
