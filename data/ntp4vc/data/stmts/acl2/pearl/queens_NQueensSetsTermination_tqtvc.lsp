;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/queens_NQueensSetsTermination_tqtvc: the N-queens finite-set
;; termination verification condition, including minimum-element removal,
;; shifted attack sets, and strict cardinal decreases. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Why3 finite set of mathematical integers is represented by a proper,
;; duplicate-free list of ACL2 integers. Set equality below is extensional, so
;; list order is irrelevant; LEN is therefore exactly finite-set cardinality.

(defun nqst-integer-set-p (set)
  (declare (xargs :measure (acl2-count set)))
  (if (consp set)
      (and
       (integerp (car set))
       (not (member-equal (car set) (cdr set)))
       (nqst-integer-set-p (cdr set)))
    (equal set nil)))

(defun nqst-member-p (element set)
  (if (member-equal element set) t nil))

(defun nqst-subset-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (nqst-member-p (car left) right)
       (nqst-subset-p (cdr left) right))
    t))

(defun nqst-set-equal-p (left right)
  (and
   (nqst-subset-p left right)
   (nqst-subset-p right left)))

(defun nqst-difference (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (if (nqst-member-p (car left) right)
          (nqst-difference (cdr left) right)
        (cons
         (car left)
         (nqst-difference (cdr left) right)))
    nil))

(defun nqst-insert (element set)
  (if (nqst-member-p element set)
      set
    (cons element set)))

(defun nqst-remove (element set)
  (declare (xargs :measure (acl2-count set)))
  (if (consp set)
      (if (equal element (car set))
          (nqst-remove element (cdr set))
        (cons
         (car set)
         (nqst-remove element (cdr set))))
    nil))

;; The empty-set value is immaterial: every use of the minimum is under the
;; source hypothesis that the finite set is nonempty.

(defun nqst-minimum (set)
  (declare (xargs :measure (acl2-count set)))
  (if (consp set)
      (if (consp (cdr set))
          (let ((tail-minimum
                 (nqst-minimum (cdr set))))
            (if (< (car set) tail-minimum)
                (car set)
              tail-minimum))
        (car set))
    0))

;; These predicates preserve the two extensional set characterizations from
;; Why3's PRED and SUCC specifications, quantifying over every integer.

(defun-sk nqst-o4-characterization-p (o4 o3)
  (forall (i)
    (implies
     (integerp i)
     (iff
      (nqst-member-p i o4)
      (and
       (<= 0 i)
       (nqst-member-p (+ i 1) o3))))))

(defun-sk nqst-o6-characterization-p (o6 o5)
  (forall (i)
    (implies
     (integerp i)
     (iff
      (nqst-member-p i o6)
      (and
       (<= 1 i)
       (nqst-member-p (- i 1) o5))))))

;; O8 is intentionally retained although unused, exactly as in the exported
;; verification condition.

(defun-sk nqst-all-o9-p (a b c e d)
  (forall (o8 o9)
    (implies
     (and
      (integerp o8)
      (nqst-integer-set-p o9))
     (implies
      (and
       (nqst-set-equal-p
        o9
        (nqst-remove d e))
       (if (nqst-member-p d e)
           (equal (len o9)
                  (- (len e) 1))
         (equal (len o9)
                (len e))))
      (and
       (and
        (<= 0 (len e))
        (< (len o9) (len e)))
       (nqst-subset-p
        o9
        (nqst-difference
         (nqst-difference a b)
         c)))))))

(defun-sk nqst-all-o7-p (a b c e d)
  (forall (o7)
    (implies
     (nqst-integer-set-p o7)
     (implies
      (and
       (nqst-set-equal-p
        o7
        (nqst-remove d a))
       (if (nqst-member-p d a)
           (equal (len o7)
                  (- (len a) 1))
         (equal (len o7)
                (len a))))
      (and
       (and
        (<= 0 (len a))
        (< (len o7) (len a)))
       (nqst-all-o9-p a b c e d))))))

(defun-sk nqst-all-o6-p (a b c e d o5)
  (forall (o6)
    (implies
     (nqst-integer-set-p o6)
     (implies
      (nqst-o6-characterization-p o6 o5)
      (nqst-all-o7-p a b c e d)))))

(defun-sk nqst-all-o5-p (a b c e d)
  (forall (o5)
    (implies
     (nqst-integer-set-p o5)
     (implies
      (and
       (nqst-set-equal-p
        o5
        (nqst-insert d b))
       (if (nqst-member-p d b)
           (equal (len o5)
                  (len b))
         (equal (len o5)
                (+ (len b) 1))))
      (nqst-all-o6-p a b c e d o5)))))

(defun-sk nqst-all-o4-p (a b c e d o3)
  (forall (o4)
    (implies
     (nqst-integer-set-p o4)
     (implies
      (nqst-o4-characterization-p o4 o3)
      (nqst-all-o5-p a b c e d)))))

(defun-sk nqst-all-o3-p (a b c e d)
  (forall (o3)
    (implies
     (nqst-integer-set-p o3)
     (implies
      (and
       (nqst-set-equal-p
        o3
        (nqst-insert d c))
       (if (nqst-member-p d c)
           (equal (len o3)
                  (len c))
         (equal (len o3)
                (+ (len c) 1))))
      (nqst-all-o4-p a b c e d o3)))))

;; F is also unused in the source VC. Its integer type and universal scope are
;; preserved together with the universal finite-set quantifier for E.

(defun-sk nqst-all-f-and-e-p (a b c)
  (forall (f e)
    (implies
     (and
      (integerp f)
      (nqst-integer-set-p e))
     (implies
      (and
       (nqst-subset-p
        e
        (nqst-difference
         (nqst-difference a b)
         c))
       (not (equal e nil)))
      (and
       (not (equal e nil))
       (nqst-all-o3-p
        a b c e
        (nqst-minimum e)))))))

(defun-sk
  ntp4vc-pearl-queens-nqueenssetstermination-tqtvc-statement
  ()
  (forall (a o1 b o2 c)
    (implies
     (and
      (nqst-integer-set-p a)
      (nqst-integer-set-p o1)
      (nqst-integer-set-p b)
      (nqst-integer-set-p o2)
      (nqst-integer-set-p c))
     (implies
      (and
       (not (equal a nil))
       (nqst-set-equal-p
        o1
        (nqst-difference a b))
       (nqst-set-equal-p
        o2
        (nqst-difference o1 c)))
      (and
       (nqst-subset-p
        o2
        (nqst-difference
         (nqst-difference a b)
         c))
       (nqst-all-f-and-e-p a b c))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
