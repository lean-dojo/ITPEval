;; Statement-only formalization of Babel-formal artifact ideals: in an
;; arbitrary commutative ring, an arbitrarily indexed intersection of ideals
;; and the sum of two ideals are ideals. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary carrier,
;; operations, index type, family of predicates, and two individual
;; predicates. No carrier, function, family, or predicate is enumerated.

(defstub ideals-carrier-p (ring value) t)
(defstub ideals-index-member-p (index-type index) t)
(defstub ideals-zero (ring) t)
(defstub ideals-one (ring) t)
(defstub ideals-add (ring left right) t)
(defstub ideals-mul (ring left right) t)
(defstub ideals-opp (ring value) t)
(defstub ideals-family-member-p (family index value) t)
(defstub ideals-ideal-member-p (ideal value) t)

(defun-sk ideals-ring-laws-p (ring)
  (forall (a x y z)
    (and
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-carrier-p ring y))
      (and
       (ideals-carrier-p ring (ideals-add ring x y))
       (ideals-carrier-p ring (ideals-mul ring x y))
       (equal (ideals-add ring x y)
              (ideals-add ring y x))
       (equal (ideals-mul ring x y)
              (ideals-mul ring y x))
       (equal
        (ideals-opp ring (ideals-add ring x y))
        (ideals-add ring
                    (ideals-opp ring x)
                    (ideals-opp ring y)))))
     (implies
      (ideals-carrier-p ring x)
      (and
       (ideals-carrier-p ring (ideals-opp ring x))
       (equal (ideals-add ring x (ideals-zero ring)) x)
       (equal
        (ideals-add ring x (ideals-opp ring x))
        (ideals-zero ring))
       (equal (ideals-mul ring x (ideals-one ring)) x)))
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-carrier-p ring y)
           (ideals-carrier-p ring z))
      (and
       (equal
        (ideals-add ring (ideals-add ring x y) z)
        (ideals-add ring x (ideals-add ring y z)))
       (equal
        (ideals-mul ring (ideals-mul ring x y) z)
        (ideals-mul ring x (ideals-mul ring y z)))))
     (implies
      (and (ideals-carrier-p ring a)
           (ideals-carrier-p ring x)
           (ideals-carrier-p ring y))
      (equal
       (ideals-mul ring a (ideals-add ring x y))
       (ideals-add ring
                   (ideals-mul ring a x)
                   (ideals-mul ring a y)))))))

(defun ideals-commutative-ring-p (ring)
  (and
   (ideals-carrier-p ring (ideals-zero ring))
   (ideals-carrier-p ring (ideals-one ring))
   (ideals-ring-laws-p ring)))

(defun-sk ideals-ideal-closure-p (ring ideal)
  (forall (a x y)
    (and
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-carrier-p ring y)
           (ideals-ideal-member-p ideal x)
           (ideals-ideal-member-p ideal y))
      (ideals-ideal-member-p ideal (ideals-add ring x y)))
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-ideal-member-p ideal x))
      (ideals-ideal-member-p ideal (ideals-opp ring x)))
     (implies
      (and (ideals-carrier-p ring a)
           (ideals-carrier-p ring x)
           (ideals-ideal-member-p ideal x))
      (ideals-ideal-member-p ideal (ideals-mul ring a x))))))

(defun ideals-is-ideal-p (ring ideal)
  (and
   (ideals-ideal-member-p ideal (ideals-zero ring))
   (ideals-ideal-closure-p ring ideal)))

(defun-sk ideals-family-entry-closure-p (ring family index)
  (forall (a x y)
    (and
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-carrier-p ring y)
           (ideals-family-member-p family index x)
           (ideals-family-member-p family index y))
      (ideals-family-member-p
       family index (ideals-add ring x y)))
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-family-member-p family index x))
      (ideals-family-member-p
       family index (ideals-opp ring x)))
     (implies
      (and (ideals-carrier-p ring a)
           (ideals-carrier-p ring x)
           (ideals-family-member-p family index x))
      (ideals-family-member-p
       family index (ideals-mul ring a x))))))

(defun ideals-family-entry-is-ideal-p (ring family index)
  (and
   (ideals-family-member-p
    family index (ideals-zero ring))
   (ideals-family-entry-closure-p ring family index)))

(defun-sk ideals-family-all-ideals-p
    (ring index-type family)
  (forall (index)
    (implies
     (ideals-index-member-p index-type index)
     (ideals-family-entry-is-ideal-p ring family index))))

(defun-sk ideals-intersection-member-p
    (index-type family value)
  (forall (index)
    (implies
     (ideals-index-member-p index-type index)
     (ideals-family-member-p family index value))))

(defun-sk ideals-intersection-closure-p
    (ring index-type family)
  (forall (a x y)
    (and
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-carrier-p ring y)
           (ideals-intersection-member-p index-type family x)
           (ideals-intersection-member-p index-type family y))
      (ideals-intersection-member-p
       index-type family (ideals-add ring x y)))
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-intersection-member-p index-type family x))
      (ideals-intersection-member-p
       index-type family (ideals-opp ring x)))
     (implies
      (and (ideals-carrier-p ring a)
           (ideals-carrier-p ring x)
           (ideals-intersection-member-p index-type family x))
      (ideals-intersection-member-p
       index-type family (ideals-mul ring a x))))))

(defun ideals-intersection-is-ideal-p
    (ring index-type family)
  (and
   (ideals-intersection-member-p
    index-type family (ideals-zero ring))
   (ideals-intersection-closure-p ring index-type family)))

(defun-sk ideals-sum-member-p
    (ring ideal1 ideal2 value)
  (exists (left right)
    (and
     (ideals-carrier-p ring left)
     (ideals-carrier-p ring right)
     (ideals-ideal-member-p ideal1 left)
     (ideals-ideal-member-p ideal2 right)
     (equal value (ideals-add ring left right)))))

(defun-sk ideals-sum-closure-p (ring ideal1 ideal2)
  (forall (a x y)
    (and
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-carrier-p ring y)
           (ideals-sum-member-p ring ideal1 ideal2 x)
           (ideals-sum-member-p ring ideal1 ideal2 y))
      (ideals-sum-member-p
       ring ideal1 ideal2 (ideals-add ring x y)))
     (implies
      (and (ideals-carrier-p ring x)
           (ideals-sum-member-p ring ideal1 ideal2 x))
      (ideals-sum-member-p
       ring ideal1 ideal2 (ideals-opp ring x)))
     (implies
      (and (ideals-carrier-p ring a)
           (ideals-carrier-p ring x)
           (ideals-sum-member-p ring ideal1 ideal2 x))
      (ideals-sum-member-p
       ring ideal1 ideal2 (ideals-mul ring a x))))))

(defun ideals-sum-is-ideal-p (ring ideal1 ideal2)
  (and
   (ideals-sum-member-p
    ring ideal1 ideal2 (ideals-zero ring))
   (ideals-sum-closure-p ring ideal1 ideal2)))

(defun-sk ideals-inter-is-ideal-statement ()
  (forall (ring index-type family)
    (implies
     (and
      (ideals-commutative-ring-p ring)
      (ideals-family-all-ideals-p
       ring index-type family))
     (ideals-intersection-is-ideal-p
      ring index-type family))))

(defun-sk ideals-sum-is-ideal-statement ()
  (forall (ring ideal1 ideal2)
    (implies
     (and
      (ideals-commutative-ring-p ring)
      (ideals-is-ideal-p ring ideal1)
      (ideals-is-ideal-p ring ideal2))
     (ideals-sum-is-ideal-p ring ideal1 ideal2))))

(value-triple :itpeval-statement-checked)
:q
