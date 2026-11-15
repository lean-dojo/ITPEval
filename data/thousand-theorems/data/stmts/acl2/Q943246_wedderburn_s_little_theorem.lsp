;; Statement-only formalization of thousand-theorems corpus artifact Q943246,
;; "Wedderburn's little theorem": every finite division ring has commutative
;; multiplication and therefore carries a field structure. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent an arbitrary carrier and its
;; division-ring operations. The ring tag permits independent structures.

(defstub q943246-member-p (ring value) t)
(defstub q943246-zero (ring) t)
(defstub q943246-one (ring) t)
(defstub q943246-add (ring left right) t)
(defstub q943246-multiply (ring left right) t)
(defstub q943246-negate (ring value) t)
(defstub q943246-inverse (ring value) t)

;; Finiteness is an internal existential assertion that some duplicate-free
;; true list enumerates exactly the carrier; the enumeration is not an
;; additional parameter of the theorem statement.

(defun-sk q943246-enumerates-carrier-p (ring enumeration)
  (forall (value)
    (iff
     (q943246-member-p ring value)
     (member-equal value enumeration))))

(defun q943246-carrier-enumeration-p (ring enumeration)
  (and
   (true-listp enumeration)
   (no-duplicatesp-equal enumeration)
   (q943246-enumerates-carrier-p ring enumeration)))

(defun-sk q943246-finite-carrier-p (ring)
  (exists (enumeration)
    (q943246-carrier-enumeration-p ring enumeration)))

;; These are the additive-group, multiplicative-group-with-zero, and
;; distributive laws of a division ring, restricted to the abstract carrier.

(defun-sk q943246-division-ring-laws-p (ring)
  (forall (x y z)
    (let* ((zero (q943246-zero ring))
           (one (q943246-one ring))
           (negative-x (q943246-negate ring x))
           (inverse-x (q943246-inverse ring x))
           (x-plus-y (q943246-add ring x y))
           (y-plus-z (q943246-add ring y z))
           (x-times-y (q943246-multiply ring x y))
           (y-times-z (q943246-multiply ring y z)))
      (and
       (implies
        (q943246-member-p ring x)
        (and
         (q943246-member-p ring negative-x)
         (q943246-member-p ring inverse-x)
         (equal (q943246-add ring x zero) x)
         (equal (q943246-add ring zero x) x)
         (equal (q943246-add ring x negative-x) zero)
         (equal (q943246-add ring negative-x x) zero)
         (equal (q943246-multiply ring x one) x)
         (equal (q943246-multiply ring one x) x)
         (equal (q943246-multiply ring x zero) zero)
         (equal (q943246-multiply ring zero x) zero)
         (implies
          (not (equal x zero))
          (and
           (equal
            (q943246-multiply ring x inverse-x)
            one)
           (equal
            (q943246-multiply ring inverse-x x)
            one)))))
       (implies
        (and
         (q943246-member-p ring x)
         (q943246-member-p ring y))
        (and
         (q943246-member-p ring x-plus-y)
         (q943246-member-p ring x-times-y)
         (equal x-plus-y (q943246-add ring y x))))
       (implies
        (and
         (q943246-member-p ring x)
         (q943246-member-p ring y)
         (q943246-member-p ring z))
        (and
         (equal
          (q943246-add ring x-plus-y z)
          (q943246-add ring x y-plus-z))
         (equal
          (q943246-multiply ring x-times-y z)
          (q943246-multiply ring x y-times-z))
         (equal
          (q943246-multiply ring x y-plus-z)
          (q943246-add
           ring
           (q943246-multiply ring x y)
           (q943246-multiply ring x z)))
         (equal
          (q943246-multiply ring x-plus-y z)
          (q943246-add
           ring
           (q943246-multiply ring x z)
           (q943246-multiply ring y z)))))))))

(defun q943246-division-ring-p (ring)
  (let ((zero (q943246-zero ring))
        (one (q943246-one ring)))
    (and
     (q943246-member-p ring zero)
     (q943246-member-p ring one)
     (not (equal zero one))
     (equal (q943246-inverse ring zero) zero)
     (q943246-division-ring-laws-p ring))))

(defun-sk q943246-commutative-multiplication-p (ring)
  (forall (x y)
    (implies
     (and
      (q943246-member-p ring x)
      (q943246-member-p ring y))
     (equal
      (q943246-multiply ring x y)
      (q943246-multiply ring y x)))))

(defun-sk thousand-theorems-q943246-wedderburn-s-little-theorem-statement ()
  (forall (ring)
    (implies
     (and
      (q943246-finite-carrier-p ring)
      (q943246-division-ring-p ring))
     (q943246-commutative-multiplication-p ring))))

(value-triple :itpeval-statement-checked)
:q
